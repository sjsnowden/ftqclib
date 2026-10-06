# Introduction to ftqclib

`index.html` is the self-contained public reading edition, intended for the site's `/intro/` route. It uses STYLE-PUBLIC, native MathML, and inline SVGs. It describes the inspected published source snapshot and identifies planned work separately.

Editable Markdown, diagrams, source-excerpt provenance, and the pinned build dependencies are in `source/`. To rebuild with Node.js 20 or newer:

```sh
cd intro/source
npm ci --ignore-scripts
npm run build
```

The build writes `intro/index.html` and `intro/build-manifest.json`. See `source/README.md` for source provenance and validation scope.

Include `intro/index.html` in the existing site's complete deployment output. This directory does not contain the rest of that website or its deployment configuration.
