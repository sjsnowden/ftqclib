# Licensing

Copyright (c) 2026 Sam Snowden.

| content | license |
|---|---|
| Lean source files (`*.lean`) | Apache License 2.0, text in [`LICENSE`](LICENSE) |
| Everything else in this repository (Markdown, TOML, JSON and other non-Lean files) | All rights reserved. No license is granted. |

The Apache License 2.0 applies to `.lean` files only. The presence of [`LICENSE`](LICENSE) at the
repository root does not extend it to any other file. Every Lean file carries the Apache header in
its first five lines.

Dependencies: Lean 4 and Mathlib are Apache 2.0 and are fetched by `lake`, not vendored; nothing of
theirs is redistributed here.
