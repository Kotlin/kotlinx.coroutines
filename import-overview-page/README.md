# Import Observatory

Interactive, offline-capable webpage for the complete `../import-overview` evidence snapshot. No backend, telemetry collector, Gradle sync, runtime CDN, or external font is required.

## Open

Open **`index.html` directly in a browser**. Generated `app.js` and `data.js` are included, so Node and Python are not needed to view it.

Alternatively, from this directory:

```sh
python3 -m http.server 8080 --bind 127.0.0.1 --directory ..
```

Visit <http://localhost:8080/import-overview-page/>. Serve the parent directory so original evidence links work. Keep `import-overview-page` and `import-overview` next to each other when sharing; the interactive views are self-contained, but original-file links use the sibling directory.

## Explore

- **Pipeline:** filter 26 work items by text, owner, or logical phase; select cards for conditions, reuse details, and source excerpts. Multiple cards with one W-ID represent shared ownership, not repeated execution. Collector ownership is retained in item details; telemetry is cross-cutting.
- **Trace explorer:** inspect both traces and all 971 canonical spans, with search, process/thread filters, minimum duration, error tags, ordering, pagination, horizontal zoom, parent links, and recorded attributes. Expand repeated HTTP pairs to inspect requests.
- **Benchmarks:** compare all four datasets by scenario and metric; show individual iterations, observed ranges, missing runs, warm-ups, and original scenario definitions. Warm-ups are excluded by default.
- **Investigation:** read all ten hypotheses with evidence and validation criteria.
- **Documentation:** search and read all original Markdown documents with in-page navigation. The original Mermaid sequence source is expandable; the Pipeline tab provides the interactive ownership diagram.
- **Evidence archive:** search captured source excerpts or open every original file, including manifests, raw traces, reports, scripts, and derived JSON.

Source-backed paths, conceptual order, measured spans, and hypotheses are deliberately separate. Widths in the ownership map do not encode time. Trace scopes overlap; uncovered intervals are not CPU time. Missing benchmark samples are never zero. Different environments and uncontrolled cache states prevent causal speedup claims.

## Update and test

Build requirements: Node.js 22+ (for the pinned packages), npm, and Python 3.9+.

```sh
npm ci
npm run build
npm test
npx playwright install chromium
npm run test:browser
```

`build_data.py` reads the source directory without altering it and deterministically rebuilds `data.js`: complete Markdown and top-level JSON catalogs, plus an inventory of all source files. `src/app.js` and `src/core.js` bundle to `app.js`; `styles.css` is loaded directly. Commit regenerated assets when changing source or evidence. No original 17 MB trace is duplicated into the page bundle.

`build.mjs` also preserves the bundled Markdown renderer and sanitizer licenses in `THIRD_PARTY_LICENSES.txt`.

Tests cover snapshot fidelity, missing data, warm-up handling, parent hierarchies, path resolution, offline browser loading, filtering, dialogs, navigation, raw-file access, and mobile layout. Browser screenshots are written under ignored `test-results/`.

## Publishing precautions

This snapshot contains source excerpts, machine paths, process attributes, and internal logs. Review sharing permissions and sensitive metadata before publishing. The optional local server exposes the repository to localhost only. Markdown is sanitized before rendering; raw files are linked as evidence, not executed by the page.