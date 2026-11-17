#!/usr/bin/env bash

# This file is part of midnight-zk.
# Copyright (C) Midnight Foundation
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# You may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Commit the STAGED changes onto <branch> as a GitHub-signed commit, via the
# createCommitOnBranch GraphQL API. Commits made with GITHUB_TOKEN are signed by
# GitHub's web-flow key and show as Verified, so they satisfy branch protection
# that requires signed commits - which a plain CI `git commit` does not.
#
# Stage what to commit first (git add <paths>), exactly as for a normal commit;
# this reads `git diff --cached`. The branch must already exist on the remote.
# The commit is authored as the token identity (github-actions[bot]); no local
# `git push` is needed, as the API moves the remote tip. Local HEAD is then reset
# to the new commit so a following commit in the same job starts clean.
#
# Honors DRY_RUN=true: logs the file changes and makes no commit.
#
# Args: $1  branch          $2  commit message headline
#       $3  optional commit message body (e.g. a Signed-off-by trailer)
# Env:  GH_TOKEN/GITHUB_TOKEN (contents:write), GITHUB_REPOSITORY
set -euo pipefail

BRANCH="$1"
MESSAGE="$2"
BODY="${3:-}"

# expectedHeadOid = the current remote tip, so sequential commits in one job
# chain correctly (each lands on the previous one's result, not a stale local).
EXPECTED_OID=$(git ls-remote origin "refs/heads/${BRANCH}" | cut -f1)
if [ -z "$EXPECTED_OID" ]; then
  echo "::error::branch ${BRANCH} does not exist on the remote"; exit 1
fi

# Build additions (full new contents, base64) and deletions from the staged set,
# one compact JSON object per line, into temp files. --no-renames so a rename is
# a delete + add; quotepath off for safe path bytes. Everything flows through
# files (jq --rawfile/--slurpfile, gh --input) so no potentially large content
# (e.g. Cargo.lock's base64) is ever passed on argv, which would exceed ARG_MAX.
adds_file="$(mktemp)"; dels_file="$(mktemp)"; b64_file="$(mktemp)"; body_file="$(mktemp)"
trap 'rm -f "$adds_file" "$dels_file" "$b64_file" "$body_file"' EXIT
while IFS=$'\t' read -r status path; do
  if [ "$status" = "D" ]; then
    jq -cn --arg p "$path" '{path:$p}' >> "$dels_file"
  else
    git show ":0:${path}" | base64 | tr -d '\n' > "$b64_file"
    jq -cn --arg p "$path" --rawfile c "$b64_file" '{path:$p,contents:$c}' >> "$adds_file"
  fi
done < <(git -c core.quotepath=false diff --cached --name-status --no-renames "$EXPECTED_OID")

if [ ! -s "$adds_file" ] && [ ! -s "$dels_file" ]; then
  echo "No staged changes for ${BRANCH}; nothing to commit."; exit 0
fi

if [ "${DRY_RUN:-false}" = "true" ]; then
  echo "[dry-run] would commit to ${BRANCH}: \"${MESSAGE}\""
  echo "  additions:"; jq -r '.path' "$adds_file" | sed 's/^/    /' || true
  echo "  deletions:"; jq -r '.path' "$dels_file" | sed 's/^/    /' || true
  exit 0
fi

QUERY='mutation($input: CreateCommitOnBranchInput!) {
  createCommitOnBranch(input: $input) { commit { oid url } }
}'

# --slurpfile reads each temp file's JSON-lines into an array (empty file -> []).
jq -n \
    --arg repo "$GITHUB_REPOSITORY" --arg branch "$BRANCH" --arg msg "$MESSAGE" \
    --arg body "$BODY" --arg oid "$EXPECTED_OID" --arg query "$QUERY" \
    --slurpfile adds "$adds_file" --slurpfile dels "$dels_file" \
    '{query:$query, variables:{input:{
        branch:{repositoryNameWithOwner:$repo, branchName:$branch},
        message:({headline:$msg} + (if $body == "" then {} else {body:$body} end)),
        expectedHeadOid:$oid,
        fileChanges:{additions:$adds, deletions:$dels}}}}' > "$body_file"

NEW_OID=$(gh api graphql --input "$body_file" --jq '.data.createCommitOnBranch.commit.oid')

echo "Committed ${NEW_OID} to ${BRANCH} (verified)."
# Advance local HEAD to the new commit (so a later tag/commit in this job is
# based on it). --mixed, like a plain `git commit`: resets HEAD and index but
# leaves the working tree, preserving unstaged changes (e.g. a cargo-touched
# Cargo.lock) that a following build step may rely on.
git fetch --quiet origin "$BRANCH"
git reset --mixed "$NEW_OID"
