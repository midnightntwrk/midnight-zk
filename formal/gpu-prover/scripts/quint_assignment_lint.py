#!/usr/bin/env python3
# This file is part of MIDNIGHT-ZK.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Advisory lexical lint for ungrouped assignment RHS Boolean operators.

This is not a Quint parser or a model-correctness check. Producer parse/typecheck
and scripted witnesses remain required. Parenthesized subexpressions and block
forms are allowed. Comments and strings retain offsets but contribute no tokens.
"""
import argparse
import pathlib
import re


def masked(text: str) -> str:
    chars = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith('//', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text.startswith('/*', i):
            depth = 1
            i += 2
            while i < len(text) and depth:
                if text.startswith('/*', i):
                    depth += 1
                    i += 2
                elif text.startswith('*/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(text))):
            if text[j] != '\n':
                chars[j] = ' '
    return ''.join(chars)


def findings(text: str) -> list[int]:
    """Return one-based assignment lines with ungrouped infix and/or."""
    code = masked(text)
    tokens = list(re.finditer(r"[A-Za-z_][A-Za-z_0-9]*'?|==|!=|=>|[^\s]", code))
    result = []
    for i, token in enumerate(tokens[:-1]):
        if not token.group().endswith("'") or tokens[i + 1].group() != '=':
            continue
        # Conditional and match bodies have their own expression boundaries.
        # Leave those constructs to the producer parser rather than flag their
        # legitimate internal Boolean expressions as ungrouped assignment RHS.
        if i + 2 < len(tokens) and tokens[i + 2].group() in ('if', 'match'):
            continue
        depth = 0
        for following in tokens[i + 2:]:
            word = following.group()
            if depth == 0 and (word in ',;})]' or word in ('action', 'run', 'val', 'def')):
                break
            if depth == 0 and word in ('and', 'or'):
                # Block operators group their own operands and are supported.
                end = following.end()
                if not re.match(r'\s*\{', code[end:]):
                    result.append(code.count('\n', 0, token.start()) + 1)
                    break
            if word in '({[':
                depth += 1
            elif word in ')}]':
                depth -= 1
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('models', type=pathlib.Path, nargs='+')
    args = parser.parse_args()
    count = 0
    for path in args.models:
        for line in findings(path.read_text()):
            print(f'{path}:{line}: advisory: group assignment RHS and/or with blocks or whole-RHS parentheses')
            count += 1
    print(f'assignment lint: {count} advisories (not proof or producer validation)')


if __name__ == '__main__':
    main()
