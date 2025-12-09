# Gemini Agent Requirements

## Proof & Code Expectations
- Match the Lean-first workflow documented in `AGENTS.md`: every behavioral change needs accompanying theorems or lemmas that capture the intended invariant.
- Treat `lake build` as non-negotiable before sending results back, and run `lake test` (plus `lake exe slowTests` when SAN/PGN/perft code moves) whenever your changes touch those areas.

## Docs & Traceability
- Mirror Claude’s documentation rules: update README sections that describe any notation or parser surfaces you touch, and cite relevant specs (FEN/SAN/PGN/FIDE) when you justify a change.
- Call out newly proven lemmas in PR descriptions so reviewers can map code edits to their formal guarantees.

## MCP Integration
- Before burning lots of tokens on symbol pushing, hand the goal to the `solve` MCP server. It’s optimized for grindy proof obligations and usually returns a usable derivation faster than native Gemini reasoning, so hook it into the loop early and treat the saved tokens as budget for higher-level exploration.
- Reference the `solve` output in your Lean proof comments if it guided the final script—this makes it easier for other contributors to replay or extend the approach and documents when MCP assistance was used.
