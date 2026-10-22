# Plan quality rubrics

- Make sure the plans are in the correct format: the command `lake exe tracker lint` should pass.
- A module plan's `desc` field should contain overall design notes.
- A module plan should contain a list of planned declarations (the key Lean definitions and theorem statements) in logical progression order.
- The backbone and surface layers should be appropriately delineated, and their respective plans should meet the quality rubrics specified for each.
  - Ideally, each surface result should be easy to prove from the general results planned in the backbone.

## Backbone library structure rubrics

- The backbone need not to adhere to the structure of the source material.
- The directory structure of the module plans should reflect a Mathlib-style Lean module hierarchy.
  - Do not put too many files in a single flat folder; aim for a balanced and logical organization.
- Structure results in their natural levels of generality.
  - The natural level of generality is determined by *which structures are being used* downstream. For example, if a textbook theory utilizes only the vector space and topological structure of $\mathbb R^n$, it may be generalized to Banach spaces, or even topological vector spaces.
  - When in doubt, multiple levels of generality can be provided, with more concrete interfaces instantiating more general ones.
- Minimize duplication: something may have been formalized elsewhere in Mathlib or within this project, or the same logic is repeated in multiple proofs.
- Respect symmetry: if dual concepts or theorems must be present, make sure they have symmetric naming and placement within the codebase. When possible, delegate the proof of one to the other rather than duplicating effort.
- Aim for easy extensibility, with respect to anticipated future demands (e.g. integrating another textbook on the same topic into this project, or formalizing another research paper in the same area using this project). 
- Declarations should have systematic naming conventions, [following Mathlib](https://leanprover-community.github.io/contribute/naming.html).

## Surface library structure rubrics

- The surface must adhere to the structure of the source material.
- Each surface declaration should be placed in the module plan `NumlibSurface.<source>.[Chapter<number>].[Section<number>]`.
  - Some textbooks may use "Part" instead of "Chapter"; we normalize to "Chapter" in the module plan naming.
  - Papers that do not have chapters can skip the "Chapter" part in the naming scheme.
- Each declaration that has a corresponding numbered item in the source material should match exactly against those, except documented fixes for incorrect statements in the source material.
- Delegating to duplicate statements in the backbone or Mathlib is allowed and encouraged.
- Declarations should be named consistently with the source material, using the same terminology and numbering.
