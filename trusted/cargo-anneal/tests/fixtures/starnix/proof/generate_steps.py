# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Produce candidate execution witnesses; Lean checks every source transition."""

import argparse
import copy
import json
from pathlib import Path

HEADER = '-- Copyright 2026 The Fuchsia Authors\n--\n-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n-- This file may not be copied, modified, or distributed except according to\n-- those terms.\n\n'

# Enumerate concrete control choices while retaining the u64 input as a
# symbolic parameter. The generated theorem must cover every value, not a
# finite sample; Lean checks the emitted transitions against sourceBody.
def produce(body, flag, width):
    markers = set()
    for block in body['blocks']:
        for stmt in block['statements']:
            if stmt['kind'] in ('storage_live', 'storage_dead'):
                markers.add(stmt['local'])
    locals_ = [('dead' if i in markers else 'uninit', None)
               for i in range(len(body['local_tys']))]
    locals_[1:4] = [('value', (str(flag), flag)),
                    ('value', (str(width), width)),
                    ('value', ('value', None))]
    block = position = 0
    states = []

    # Concrete values choose branches; symbolic expressions only describe
    # candidate states. These assertions restrict this producer, while its
    # generated rfl obligations still establish the actual source behavior.
    def operand(op):
        kind = op['kind']
        if kind == 'constant':
            return str(op['bits']), op['bits']
        index = op['local']
        assert locals_[index][0] == 'value', (index, locals_[index])
        value = locals_[index][1]
        if kind == 'move':
            locals_[index] = ('uninit', None)
        else:
            assert kind == 'copy'
        return value

    def rvalue(rv):
        kind = rv['kind']
        if kind == 'use':
            return operand(rv['operand'])
        if kind == 'discriminant':
            index = rv['local']
            assert locals_[index][0] == 'value'
            value = locals_[index][1][1]
            table = body['local_tys'][index]['discriminants']
            return str(table[value]), table[value]
        assert kind == 'binary'
        left, left_known = operand(rv['left'])
        right, right_known = operand(rv['right'])
        op = rv['op']
        if op == 'bit_and':
            return f'({left} &&& {right})', None
        if op == 'bit_or':
            return f'({left} ||| {right})', None
        assert op in ('shl', 'shr') and right_known is not None
        amount = right_known % 64
        operator = '<<<' if op == 'shl' else '>>>'
        return f'({left} {operator} ({amount} : Nat))', None

    while True:
        states.append((block, position, copy.deepcopy(locals_)))
        current = body['blocks'][block]
        if position < len(current['statements']):
            stmt = current['statements'][position]
            kind = stmt['kind']
            if kind == 'assign':
                result = rvalue(stmt['value'])
                locals_[stmt['local']] = ('value', result)
            elif kind == 'storage_live':
                locals_[stmt['local']] = ('uninit', None)
            elif kind == 'storage_dead':
                locals_[stmt['local']] = ('dead', None)
            else:
                assert kind == 'nop'
            position += 1
            continue
        term = current['terminator']
        if term['kind'] == 'ret':
            break
        if term['kind'] == 'goto':
            block = term['block']
        else:
            assert term['kind'] == 'switch_int'
            _, key = operand(term['operand'])
            assert key is not None
            block = dict(term['targets']).get(key, term['otherwise'])
        position = 0

    # This witness records the source's actual result, including after a
    # mutation. ProductionEndpoints separately applies the fixed expected value;
    # keeping those duties apart lets CI positively check each generated path.
    label = ('be' if flag else 'le') + str(8 << width)
    # Witness the source's actual result. Fixed byte-reversal endpoints live
    # in a separate module, so checking these transitions does not assume the
    # property that a mutation is intended to violate.
    assert locals_[0][0] == 'value'
    output = locals_[0][1][0]
    source = ''
    for i, (b, p, slots) in enumerate(states):
        source += f'private def {label}_state{i} (value : Word) : State :=\n  ⟨{b}, {p}, [\n'
        terms = [f'.value {x[1][0]}' if x[0] == 'value' else '.' + x[0]
                 for x in slots]
        for j in range(0, len(terms), 5):
            source += '    ' + ', '.join(terms[j:j + 5])
            if j + 5 < len(terms):
                source += ','
            source += '\n'
        source += '  ]⟩\n\n'
    last = len(states) - 1
    source += f'''private theorem {label}_suffix{last} (value : Word) :
    Executes sourceBody ({label}_state{last} value) ({output}) :=
  .ret (by rfl)

'''
    for i in range(last - 1, -1, -1):
        source += f'''private theorem {label}_suffix{i} (value : Word) :
    Executes sourceBody ({label}_state{i} value) ({output}) :=
  .next (by rfl) ({label}_suffix{i + 1} value)

'''
    source += f'''theorem {label}_actual (value : Word) :
    Safe sourceBody [{flag}, {width}, value] ∧
      Returns sourceBody [{flag}, {width}, value] ({output}) := by
  have start : initial sourceBody [{flag}, {width}, value] =
      {label}_state0 value := by rfl
  have execution : Executes sourceBody
      (initial sourceBody [{flag}, {width}, value]) ({output}) := by
    rw [start]
    exact {label}_suffix0 value
  exact ⟨executes_safe execution, executes_returns execution⟩

'''
    return source, len(states)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture', type=Path, help='Typed capture.json input')
    parser.add_argument('output', type=Path, help='Candidate Lean proof module')
    args = parser.parse_args()
    with args.capture.open() as source:
        captured = json.load(source)
    bodies = captured['program']['bodies']
    if len(bodies) != 1:
        raise ValueError('The fixture requires one selected production body')
    parts = []
    count = 0
    for flag in (0, 1):
        for width in range(4):
            part, length = produce(bodies[0], flag, width)
            parts.append(part)
            count += length
    args.output.write_text(HEADER + """prelude
import InitialCache

namespace ProductionSteps

open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction

""" + ''.join(parts) + 'end ProductionSteps\n')
    print(f'Wrote {count} candidate state witnesses to {args.output}')


if __name__ == '__main__':
    main()
