#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check source headers, Action pins, and local Markdown targets offline.

Run in the pinned static shell described by ci/check_static.sh. Git supplies
tracked and nonignored new files, so generated build trees are not inputs.
Registered binary assets are exempt from text checks. Header validation checks
structure and a positive year with four digits, without inferring dates from
Git or the clock. Authors and reviewers establish each file's actual creation
year and preserve existing attribution.

Local Markdown paths follow GitHub's repository-file link rules: a leading slash
selects the repository root; other paths start at the Markdown file's directory.
External URLs and heading fragments are outside the link check's scope.
"""

import argparse
from html.parser import HTMLParser
from pathlib import Path
import os
import re
import subprocess
import sys
from urllib.parse import unquote, urlsplit


LICENSE = (
    "Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n"
    "<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n"
    "license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n"
    "This file may not be copied, modified, or distributed except according to\n"
    "those terms."
)

COMMENT_PREFIXES = {
    ".md": "html",
    ".rs": "//",
    ".lean": "--",
    ".py": "#",
    ".sh": "#",
    ".yml": "#",
    ".yaml": "#",
    ".toml": "#",
    ".nix": "#",
    ".sha256": "#",
}

# Keep binary exemptions explicit so unknown text formats and malformed UTF-8
# source still produce diagnostics.
BINARY_ASSET_SUFFIXES = {
    ".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".bin",
}


class CheckError(Exception):
    """An input or required tool could not be checked."""


def parsers():
    try:
        import yaml
        from markdown_it import MarkdownIt
    except ImportError as error:
        raise CheckError(
            "required parsers unavailable; run "
            "nix develop .#static --command ./ci/check_static.sh "
            f"({error})"
        ) from error
    return yaml, MarkdownIt("commonmark")


def repository_files(root):
    try:
        top = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--show-toplevel"],
            check=True, capture_output=True, text=True,
        ).stdout.strip()
        if Path(top).resolve() != root:
            raise CheckError(f"{root}: expected a Git repository root")
        output = subprocess.run(
            ["git", "-C", str(root), "ls-files", "-z", "--cached",
             "--others", "--exclude-standard"],
            check=True, capture_output=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError) as error:
        raise CheckError(f"cannot enumerate repository files: {error}") from error
    files = sorted({Path(p.decode("utf-8")) for p in output.split(b"\0") if p})
    if not files:
        raise CheckError("repository contains no checkable files")
    return files


def header_error(path, text):
    name = path.as_posix()
    # JSON and these tool-owned formats cannot carry the repository header.
    if path.suffix == ".json" or name in {"Cargo.lock", "flake.lock"}:
        return None
    if name == "trusted/lean/lean-toolchain":
        return None
    # CLAUDE.md is the existing include-only instruction, not a prose document.
    if name == "CLAUDE.md" and text == "@AGENTS.md\n":
        return None
    # License texts retain their own attribution and must remain verbatim.
    if name in {
        f"{directory}{license_name}"
        for directory in ("", "trusted/cargo-anneal/")
        for license_name in ("LICENSE-BSD", "LICENSE-APACHE", "LICENSE-MIT")
    }:
        return None
    # Skill frontmatter must be the leading metadata (AGENTS.md's exemption).
    if path.name == "SKILL.md" and text.startswith("---\n"):
        return None
    prefix = COMMENT_PREFIXES.get(path.suffix)
    # Dockerfile variants use the same hash-comment syntax. Keep registered
    # suffixes authoritative: Dockerfile.md remains a Markdown document.
    # https://docs.docker.com/reference/dockerfile/#format
    if path.name == ".gitignore" or (
        prefix is None and (
            path.name.lower() == "dockerfile"
            or path.name.lower().startswith("dockerfile.")
            or path.suffix.lower() == ".dockerfile"
        )
    ):
        prefix = "#"
    if prefix is None:
        return "no header format registered for this file type"
    if text.startswith("#!"):
        text = text.partition("\n")[2]
        if text.startswith("#\n"):
            text = text[2:]
    if prefix == "html":
        pattern = r"<!-- Copyright (?!0000)[0-9]{4} The Fuchsia Authors\n\n"
        pattern += re.escape(LICENSE + " -->\n")
    else:
        body = "\n".join(f"{prefix} {line}" for line in LICENSE.splitlines())
        pattern = re.escape(prefix)
        pattern += r" Copyright (?!0000)[0-9]{4} The Fuchsia Authors\n"
        pattern += re.escape(f"{prefix}\n{body}\n")
    if re.match(pattern, text) is None:
        return "missing or malformed leading Fuchsia copyright/license header"
    return None


def pinned_container_image(image):
    # Actions, job containers and services all select executable image bytes.
    # Share one literal pin rule so adding a route cannot weaken the digest
    # algorithms, lowercase hex or exact lengths checked on another route.
    # This accepts the existing tag/port/IPv6 spellings, not the complete OCI
    # grammar; the runner still checks image-name syntax and availability.
    return isinstance(image, str) and re.fullmatch(
        r"(?:[A-Za-z0-9]|\[)[A-Za-z0-9._:/\[\]-]*@"
        r"(?:sha256:[0-9a-f]{64}|sha384:[0-9a-f]{96}|"
        r"sha512:[0-9a-f]{128})", image,
    ) is not None


def action_errors(path, text):
    # Import after parsers() has checked required dependencies, so missing
    # PyYAML still produces the repository checker's setup diagnostic.
    from workflow_yaml import load_workflow_yaml

    data = load_workflow_yaml(text)
    if not isinstance(data, dict):
        return ["expected a workflow or Action mapping"]
    references = []
    images = []
    # GitHub selects the executable document by path, not by whichever keys
    # happen to occur in it. Workflows can themselves be named action.yml;
    # elsewhere an extra jobs mapping must not hide Action runs metadata.
    if path.parent == Path(".github/workflows"):
        jobs = data.get("jobs")
        if not isinstance(jobs, dict) or not jobs:
            return ["workflow jobs must be a nonempty mapping"]
        for job_name, job in jobs.items():
            if not isinstance(job, dict):
                return [f"job {job_name}: expected a mapping"]
            if "uses" in job:
                references.append((f"job {job_name}", job["uses"]))
            # Both documented container forms select a job's execution
            # image independently of its Action references. Other container
            # fields, such as credentials and options, are not image names.
            # https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idcontainer
            if "container" in job:
                container = job["container"]
                if isinstance(container, str):
                    images.append((f"job {job_name} container", container))
                elif isinstance(container, dict):
                    images.append((f"job {job_name} container.image",
                                   container.get("image")))
                else:
                    return [
                        f"job {job_name}: container must be a string or mapping"
                    ]
            if "services" in job:
                services = job["services"]
                if not isinstance(services, dict):
                    return [f"job {job_name}: services must be a mapping"]
                for service_name, service in services.items():
                    location = f"job {job_name} service {service_name}.image"
                    if not isinstance(service, dict):
                        return [
                            f"job {job_name} service {service_name}: "
                            "expected a mapping"
                        ]
                    image = service.get("image")
                    # GitHub documents that an empty image means "the service
                    # will not start". This exception does not cover missing
                    # fields, non-string values or later active services.
                    # https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idservicesservice_idimage
                    if image != "":
                        images.append((location, image))
            steps = job.get("steps", [])
            if not isinstance(steps, list):
                return [f"job {job_name}: steps must be a list"]
            for index, step in enumerate(steps, 1):
                if not isinstance(step, dict):
                    return [f"job {job_name} step {index}: expected a mapping"]
                if "uses" in step:
                    references.append((f"job {job_name} step {index}", step["uses"]))
    elif path.name in {"action.yml", "action.yaml"}:
        runs = data.get("runs")
        if not isinstance(runs, dict):
            return ["Action runs must be a mapping"]
        using = runs.get("using")
        if isinstance(using, str) and using.lower() == "docker":
            image = runs.get("image")
            if not isinstance(image, str):
                return ["Docker Action runs.image must be a string"]
            # Docker Action metadata selects executable images without a uses
            # step. Both surfaces need the same literal content-digest rule.
            # Local Dockerfiles remain repository build inputs; this check
            # does not inspect their FROM images or other build dependencies.
            # The runner recognizes the runtime and image prefix regardless
            # of ASCII case, before the literal pin policy is applied here.
            # https://github.com/actions/runner/blob/8cfa1049f86781d141056082d73802d56cd2b433/src/Runner.Worker/ActionManifestManager.cs#L441-L453
            # https://github.com/actions/runner/blob/8cfa1049f86781d141056082d73802d56cd2b433/src/Runner.Worker/ActionManager.cs#L1454-L1481
            if image.lower().startswith("docker://"):
                references.append(("runs.image", image))
        steps = runs.get("steps", [])
        if not isinstance(steps, list):
            return ["composite Action steps must be a list"]
        for index, step in enumerate(steps, 1):
            if not isinstance(step, dict):
                return [f"step {index}: expected a mapping"]
            if "uses" in step:
                references.append((f"step {index}", step["uses"]))
    else:
        return ["expected a workflow or Action metadata path"]
    errors = []
    for location, image in images:
        if not isinstance(image, str):
            errors.append(f"{location}: image must be a string")
        elif not pinned_container_image(image):
            errors.append(
                f"{location}: container image needs a literal image with "
                f"a full SHA-2 digest: {image}"
            )
    for location, target in references:
        if not isinstance(target, str):
            errors.append(f"{location}: uses must be a string")
        elif target.startswith("./"):
            continue
        elif target.lower().startswith("docker://"):
            # Fold only ASCII scheme case before applying the shared image
            # rule. Unicode lookalikes must not gain admission through lower().
            if (re.match(r"(?ai:docker://)", target) is None
                    or not pinned_container_image(target[len("docker://"):])):
                errors.append(
                    f"{location}: Docker Action needs a literal image with "
                    f"a full SHA-2 digest: {target}"
                )
        # A remote Action tag or branch can move after review; a full commit
        # name fixes the source selected by this workflow revision.
        elif not re.fullmatch(
            r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_./-]+)?"
            r"@[0-9a-fA-F]{40}", target,
        ):
            errors.append(f"{location}: remote Action needs a full commit SHA: {target}")
    return errors


class HTMLTargets(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.targets = []

    def handle_starttag(self, tag, attributes):
        for name, value in attributes:
            if name in {"href", "src"} and value is not None:
                self.targets.append(value)

    handle_startendtag = handle_starttag


def markdown_targets(text, markdown):
    environment = {}
    tokens = markdown.parse(text, environment)
    targets = []

    def visit(token):
        if token.type in {"link_open", "image"}:
            targets.append(token.attrGet("href") or token.attrGet("src") or "")
        if token.type in {"html_inline", "html_block"}:
            html = HTMLTargets()
            html.feed(token.content)
            targets.extend(html.targets)
        for child in token.children or []:
            visit(child)

    for token in tokens:
        visit(token)
    targets.extend(ref["href"] for ref in environment.get("references", {}).values())
    return sorted(set(targets))


def link_errors(root, path, text, markdown, repository_paths):
    errors = []
    for target in markdown_targets(text, markdown):
        url = urlsplit(target)
        if url.scheme or url.netloc or not url.path:
            continue
        decoded = unquote(url.path)
        # GitHub documents that "Links starting with `/` will be relative to
        # the repository root." Match repository-file Markdown rendering.
        # https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#relative-links
        location = (
            root / decoded.lstrip("/") if decoded.startswith("/")
            else root / path.parent / decoded
        )
        candidate = location.resolve()
        # Resolve for physical containment, but keep inventory membership
        # lexical: an ignored alias to a tracked file is still not a path
        # that GitHub can render from the proposed repository contents.
        repository_path = Path(os.path.normpath(location))
        if not candidate.is_relative_to(root):
            errors.append(f"local link leaves the repository: {target}")
        elif not candidate.exists():
            errors.append(f"missing local Markdown target: {target}")
        elif (not repository_path.is_relative_to(root)
              or repository_path.relative_to(root) not in repository_paths):
            errors.append(
                f"local Markdown target is not repository content: {target}"
            )
    return errors


def check(root):
    yaml, markdown = parsers()
    errors = []
    files = repository_files(root)
    # The same Git inventory defines checked inputs and local link targets.
    # Nonignored new files are intentional review candidates; ignored output
    # and Git metadata are not. Ancestors admit directory/root links, while
    # link_errors still requires each target to exist in this checkout.
    repository_paths = set(files)
    repository_paths.update(parent for path in files for parent in path.parents)
    workflows = [p for p in files if p.parent == Path(".github/workflows")
                 and p.suffix in {".yml", ".yaml"}]
    if not workflows:
        errors.append(".github/workflows: no workflow files found")
    for path in files:
        absolute = root / path
        if absolute.is_symlink() or not absolute.is_file():
            errors.append(f"{path}: expected an existing regular file")
            continue
        if path.suffix.lower() in BINARY_ASSET_SUFFIXES:
            continue
        try:
            text = absolute.read_text(encoding="utf-8")
            error = header_error(path, text)
            if error:
                errors.append(f"{path}: {error}")
            if path in workflows or path.name in {"action.yml", "action.yaml"}:
                errors.extend(f"{path}: {e}" for e in action_errors(path, text))
            if path.suffix == ".md":
                errors.extend(
                    f"{path}: {e}"
                    for e in link_errors(
                        root, path, text, markdown, repository_paths,
                    )
                )
        except (OSError, UnicodeError, ValueError, yaml.YAMLError, CheckError) as error:
            errors.append(f"{path}: cannot check input: {error}")
    return errors


def main():
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    root = arguments.parse_args().root.resolve()
    try:
        errors = check(root)
    except (CheckError, OSError, UnicodeError) as error:
        errors = [str(error)]
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print("Repository headers, Action pins, and local Markdown targets passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
