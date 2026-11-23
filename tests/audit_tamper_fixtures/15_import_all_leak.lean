-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- @fixture_id: 15_import_all_leak
-- @module_name: Proof.Tamper15
-- @expected_ok: false
-- @expected_category: privateInstanceLeakViaImportAll
-- @tamper_mode: compile_module_pkg

module

public import Topic.Defs
import all Topic.Defs

namespace Proof.Tamper15

public def leakedTag : Topic.Defs.SecretTag := default

end Proof.Tamper15
