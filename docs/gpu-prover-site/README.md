# GPU prover site

A static page that explains the GPU path of the midnight-proofs prover. It has seven step
animations (three.js) and renders its benchmark tables from one data file. There is no build step.

## View it

The page loads ES modules and `data/benchmarks.json`, so it needs an HTTP server. From this
directory:

```sh
python3 -m http.server 8000
```

Then open `http://localhost:8000/`.

## Files

| Path | Content |
|---|---|
| `index.html` | All text. The steps of each animation are an ordered list in this file. |
| `css/site.css` | Layout, type and the colour tokens for the light and dark themes. |
| `js/main.js` | Theme toggle, contents highlight, start of the animations. |
| `js/stage.js` | Drawing kit (three.js scene, HTML labels) and the player with its controls. |
| `js/scenes/*.js` | Five scene modules: `pipeline`, `ntt`, `msm`, `memory`, `fallback`. The page has seven figures: `fallback` draws three of them (`data-band` is `hook`, `ladder` or `client`). |
| `js/benchmarks.js` | Renders the benchmark section from the data file. |
| `data/benchmarks.json` | Every measured number on the page. |
| `vendor/` | three.js and its license. |

## Update the numbers

The page has no measured number in its HTML. Every number traces to a file in the repository,
and the page links each table to its source.

The headline comes from one measurement session. `data/session.json` is the results file of that
session, with the schema of `gpu-prover/bench/h2h/results/results.json` and these additions:

- `meta`: `source` (the in-tree results directory, which holds `RESULTS.md` and `raw/`), `tree`,
  `base`, `device`, `threads`, and `date`, `clocks` and `temperatures` (shown when not `null`).
- `h2h[].gpu.decline_reason`: the phase and reason of the counted declines as the results file
  records them, for example `msm below-min-k`; a reason without a phase, such as `below-min-k`,
  names no operation.
- `batch`: `null`, or `{ "k": 16, "sizes": { "1": { "gpu_proofs_per_s": …, "cpu_proofs_per_s": … }, … } }`.
  With data, the batch table shows in the batch section.
- `ratios`: `null`, or a list of `{ "change", "what", "ratio" }` with `ratio` a positive number.
  With data, the prover-changes section shows the accepted changes.

To publish a new session, copy its `results.json` to `data/session.json` and fill `meta`. The
page builds the per-size board, the one-proof-at-a-time table, the batch table and the ratios
from that file. The captions and column labels are in `data/benchmarks.json` (`results_h2h`,
`sequential`, `batch_session`, `cpu_changes`), with `{device}`, `{threads}`, `{base}`, `{k}` and
`{n}` filled from the session.

The other tables are older, dated measurements:

- `identity` is the sentence in the zero-knowledge section. Remove the key to remove it.
- `checks` is the table of the oracle section; its numbers come from `gpu-spec/RESULTS.md` and
  `gpu-spec/COVERAGE.md`. `"stack": true` makes a table stack its rows on a narrow screen.
- `compact_programs`, `preview` and `large_circuit` each have `label` (what the numbers were
  measured on), `columns`, `rows`, `notes` and `empty`. With no rows the page keeps the heading
  and shows the text of `empty`. A `null` cell shows "not reported".
- Their numbers come from `docs/gpu-prover/benchmarks.md`, `gpu-prover/bench/compact/results/`
  and `gpu-prover/bench/large-circuit/`. Each table has a source line under it in `index.html`.

## Animations

A scene is a function of `(step, t)`. It draws the state of step `step` at progress `t` from 0
to 1 and keeps no state of its own. The number of steps is the number of items in the ordered list
of that figure in `index.html`, so the text alternative and the animation stay in step. If you add
or remove a list item, change the scene module to match.

The NTT and MSM scenes compute the values they show (integers modulo 17, and a toy group of order
61). Each one checks its result against a direct computation and fails to start if they differ.

With `prefers-reduced-motion: reduce` the Play button is off and each step shows its final frame.
Without WebGL, or if three.js does not load, each figure shows its steps as text.

## Third-party code and requests

- three.js 0.170.0 (MIT) is in `vendor/three.module.min.js`, with its license in
  `vendor/LICENSE-three.txt`. The import map in `index.html` names the file and its integrity hash.
  To change the version, replace the file and compute the new hash:
  `openssl dgst -sha384 -binary vendor/three.module.min.js | openssl base64 -A`.
- Fonts from Google Fonts: Bricolage Grotesque, IBM Plex Sans, IBM Plex Mono. The page works with
  system fonts if they do not load.
- No analytics, no cookies. The theme choice is kept in `localStorage`.

## Links into the repository

Every link to a repository file is an `<a data-repo="PATH">`. `js/main.js` builds the address
from one constant, the `<meta name="repo-base">` in the head of `index.html`. Change that value to
point the page at another repository or branch. The same address is also written into each `href`,
so that the links work without JavaScript. Replace it there with one command:

```sh
sed -i 's#OLD_BASE#NEW_BASE#g' index.html
```

## Statements to confirm against the final code

The page states the design. Check these statements against the code before the page ships.

1. Readback. Only MSM result points, the partial bucket sums of the vendored MSM (counted, and zeroed on the host after use), base-domain transform outputs, quotient coefficients and counters return from the device. No vector on the extended domain returns.
2. The daemon routes phases to the device with the feature `cuda`. The build command in "Try it"
   uses that feature.
3. Every decline is counted, and the reply carries the decline counts of the request by phase and reason.
4. The daemon policy `keep` keeps the uploaded key copies on the device.
5. Admission on a native Linux host first activates the device and then reads its free memory. If
   it gets no reading, it counts zero bytes free. WSL2 uses a leased budget. An admitted operation
   can still decline for lack of memory.
6. Proof labels. `cpu` when the device served no call. After a served call, `gpu-degraded` when the
   request counted a fallback, else `gpu`; a degraded admission alone keeps `gpu` and lists its
   reasons in `degraded_reasons`.
7. Every test named in "Features and their tests" exists under the name given, and the text beside
   it claims no more than the test asserts.
