# The plans

The structured formalization plans in TOML, one file for each module. Check the [tracker README](../tools/tracker/README.md) for their exact schema, and the CLI commands for querying them. During a formalization project, the orchestrator agent should prefer using structured plans over prose when delegating tasks to sub-agents, and write temporary notes only as supplementary material.

Plans should contain only *key* definitions and theorems, not *every* Lean declaration. This includes important named definitions/theorems for the backbone layer, and numbered items in the books for the surface layer. After formalization is complete, some fields are superseded by the Lean declaration itself and should be removed, but the plans remain with the list of identifiers (and references to sources) as a record for which declarations are the most important.

Since the plans do not always carry descriptions (removed when superseded by Lean declarations), it is advised to use the tracker tool to query particular plans (e.g. `lake exe tracker show Krylov/CG` or `lake exe tracker ready`), or perform search within the actual Lean code.
