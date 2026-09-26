---
name: lean-build-guard
description: >-
  Guard against runaway Lean builds (a Lake package that silently clones dependencies and compiles Mathlib from source at 100 % CPU). Use before the first `lake build` / `lake env lean` in any package other than the main library, after editing a lakefile or manifest, when a second workspace shares the library's packages, or when the user reports Lean/Lake eating the CPU.
---

# lean-build-guard

Mathlib is NEVER compiled from source on this machine: every package consumes the prebuilt oleans in the main
library's `.lake/packages` (shared via `packagesDir`) or the Mathlib cache. A `lean` process compiling a file under
`.lake/packages/mathlib/Mathlib/…` is a fault, not progress.

## Before the first build of any package that is not the main library
1. `scripts/lake_preflight.sh <package dir>` — verifies `lakefile.toml`'s `packagesDir` resolves to an EXISTING
   directory that already contains `mathlib`, that any `lake-manifest.json` was generated in place (its `packagesDir`
   and path-dependency `dir` entries resolve), runs `lake env true` and refuses if that created any new directory
   (= Lake started cloning). Never copy a `lake-manifest.json` between packages (2026-09-14 incident: a copied
   manifest's relative paths resolved into a fresh location, Lake cloned all dependencies there and began compiling
   Mathlib: 100 % CPU, 4 GB, killed by hand).
2. First build with the watchdog armed: `scripts/lean_watchdog.sh &` then `lake build …`. The watchdog kills the
   `lake`/`lean` processes the moment a Mathlib (or any `.lake/packages/*`) source file is being compiled, and prints
   what it killed. A correct setup rebuilds nothing of the dependencies (a link check finishes in seconds with
   "Built … (N jobs)" where N ≈ the number of library modules already present).
3. Fresh checkout of the library itself: `lake exe cache get` BEFORE `lake build` (cache first, never a cold compile).

## Rules
- `lake update` is never run by an agent (dependency pins are the user's).
- Every build in a shared artifact tree runs under the agents-bus `lake-build` lock (one writer at a time).
- Prefer `lake env lean <file>` for single-file checks (reads oleans only) and `lake build <Module>` for targeted
  builds; a root `lake build` only by the coordinator.
- If CPU is pegged by Lean and no build was requested: `scripts/lean_watchdog.sh --once` lists and kills stray
  dependency compiles; report what was killed and why it started (usually a bad `packagesDir`/manifest path).
