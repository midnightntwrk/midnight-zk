# Contributing

Contributions are welcome. Before submitting a PR, please read through this document.

## Developer Certificate of Origin (DCO)

All contributions must include a sign-off in every commit message, certifying that you have the right to submit the code under the project license. This is done by adding a `Signed-off-by` trailer using `git commit -s`:

```
git commit -s -m "feat: your commit message"
```

This produces a commit message like:

```
feat: your commit message

Signed-off-by: Your Name <your@email.com>
```

By signing off, you agree to the [Developer Certificate of Origin (version 1.1)](https://developercertificate.org/).

If you have forgotten to sign off past commits in a PR, you can amend them:

```bash
# Amend the last commit
git commit --amend -s --no-edit

# Or rebase to sign off multiple commits (replace N with the number of commits)
git rebase --signoff HEAD~N
```

A DCO GitHub App runs on every pull request and will block merges until all commits are signed off.

### Automating sign-off

To avoid having to remember `-s` on every commit, install a `prepare-commit-msg` hook in your clone of this repo that appends the sign-off automatically:

```bash
cat > .git/hooks/prepare-commit-msg <<'EOF'
#!/bin/sh
NAME=$(git config user.name)
EMAIL=$(git config user.email)
grep -qs "^Signed-off-by: " "$1" || printf "\nSigned-off-by: %s <%s>\n" "$NAME" "$EMAIL" >> "$1"
EOF
chmod +x .git/hooks/prepare-commit-msg
```

After installing the hook, every `git commit` in this repo will include a `Signed-off-by` trailer automatically. Make sure your `user.name` and `user.email` are set correctly, since the hook certifies the DCO on your behalf for every commit.

## Before you start

Search the issue tracker to see if your bug or feature request already exists. For larger changes - refactors, new subsystems, significant API changes - open an issue first and discuss it with us.

## Requirements

**Sign your commits.** All commits must be signed.

**Update the CHANGELOG.** Every crate you modify must include a corresponding entry in its `CHANGELOG.md` describing what changed and why. Each `CHANGELOG.md` lives in the crate’s own folder.


**Keep it simple.** Write the least code that solves the problem. Short, obvious, easy to maintain. Avoid clever solutions. We value code that is straightforward enough that reviewing it doesn't take longer than writing it would have.

**Match the style.** Follow the conventions already in the codebase - naming, formatting, structure.

**Document your functions.** Public functions need doc comments. Be concise and accurate.

**Add tests.** New functionality should come with tests that cover the expected behavior.

**License header.** All new files should include:

```
// This file is part of <REPOSITORY NAME>.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
```

## Questions

Open an issue and we'll get back to you.
