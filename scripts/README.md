# scripts

## check-generic.sh

`scripts/check-generic.sh` fails (exit 1) when a tracked file has a private
name or a machine-local path in it. It prints one `file:line: reason` row per
finding. Line 0 means the file name. CI runs it on every pull request
(`.github/workflows/check-generic.yml`).

```sh
scripts/check-generic.sh                            # tracked files
CHECK_GENERIC_UNTRACKED=1 scripts/check-generic.sh  # also untracked, not ignored files
scripts/check-generic.test.sh                       # test of the check
```

### Hash scheme

The banned names are not in the tree in clear text.
`scripts/generic-denylist.sha256` holds one SHA-256 digest (lowercase hex) of
each banned name, in lowercase. Lines that start with `#` are comments.

The script splits each file name and each line of each text file into tokens
and compares the SHA-256 digest of each lowercase token with the list:

- each run of `[A-Za-z0-9_-]`,
- each part of a run split at `-` and `_`,
- each sequence of 2 to 4 neighbouring parts joined with `-`,
- each camelCase or digit part (`FooBar` gives `foo` and `bar`).

A name matches only as a whole token. A short banned name does not match
inside a longer word, so `cod` would not match `encoding`.

The script also fails on the path patterns `/home/`, `~/`, `/Users/`,
`/mnt/c` and `.cache/mgpu`. The tool homes `~/.cargo` and `~/.rustup` are
allowed.

Binary files (with a NUL byte) are skipped. `EXCLUDE_PATHS` in the script
lists skipped paths, each with its reason. The script, its test and this
README skip only the path patterns, because they must spell them out.

### Add a name

```sh
printf %s 'newname' | tr '[:upper:]' '[:lower:]' | sha256sum | cut -d' ' -f1 \
  >> scripts/generic-denylist.sha256
scripts/check-generic.test.sh && scripts/check-generic.sh
```

Use the bare name with no newline. Write a name of several words with `-`
(`a-b`); it then also matches `a_b` and `x-a-b-y`. Do not put the name in a
commit message or a comment.
