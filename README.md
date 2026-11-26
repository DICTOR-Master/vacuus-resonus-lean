# Planes Through the Centre of the Permutohedron: Faces, Vacuus Plates and Their Count, in Lean

Lean 4 (v4.37.0-rc1; Mathlib at the commit pinned in `lakefile.toml`) proofs about the permutohedron for DICTO's
paper #120, *The Vacuus and the Resonus: Form and Emptiness in the Planes of Polyhedra* (doi:10.5281/zenodo.24521888): its
faces from ordered partitions are exposed, of dimension `n - m`; the plane through the centre and each ridge (Theorem 3 (i));
when two ridges share that plane (Theorem 3 (ii)); the number of such planes (Theorem 3 (iii), OEIS A402191); and the planes
through the centre parallel to the facets, their number, and which of them pass through ridges. Statements: `Challenge.lean`;
proofs: `Solution.lean` from the library `PermFaces/`, which uses TauCeti's formalization of Rado's theorem (three files
copied unchanged except import paths into `Vendor/TauCeti/`; see `NOTICE`). Description and sources: `formalization.yaml`.
With Claude (Anthropic).
