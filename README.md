# Oliver Friedmann mission statement packages

These packages prepare three papers for Prove2Me research-paper missions. All 6 definition modules and 29 open theorem targets passed local elaboration against the pinned environment; all three draft packets passed offline validation. Each mission has its own goal and supporting targets; foundational models may be shared. The targets are statements to prove. Their `sorry` bodies do not represent completed proofs.

| Paper | Authors | Role |
| --- | --- | --- |
| [An Exponential Lower Bound for the Latest Deterministic Strategy Iteration Algorithms](https://lmcs.episciences.org/1026), LMCS, 2011 | Oliver Friedmann | The journal treatment of deterministic strategy improvement, following the LICS 2009 work. |
| [An exponential lower bound for Cunningham's rule](https://doi.org/10.1007/s10107-016-1008-4), Mathematical Programming, 2017 | David Avis and Oliver Friedmann | History-dependent cyclic pivot selection. |
| [An exponential lower bound for Zadeh's pivot rule](https://doi.org/10.1007/s10107-022-01848-x), Mathematical Programming, 2023; online 2022 | Yann Disser, Oliver Friedmann and Alexander V. Hopp | The later exponential result, with its stated tie-breaking conventions. |

The STOC 2011 Best Paper Award belongs to Friedmann, Hansen and Zwick's randomized-pivoting paper. The 2012 Tucker Prize recognizes Friedmann's dissertation. The randomized-pivoting line and the original 2011 Zadeh construction require their correction literature; see the source notes rather than copying the supplied biography into a mission. Primary sources: [Friedmann's publication list](https://oliverfriedmann.com/science/publications/), [Tucker Prize citation](https://mathopt.zib.de/?nav=tucker_2012), [Random-Facet erratum](https://arxiv.org/abs/1410.7871), [2019 Zadeh correction](https://doi.org/10.1007/978-3-030-17953-3_13).

## Files and verification

`Definitions/` contains the models, without unproved declarations. `Theorems/` contains the open goals and milestones. `mission-data/` holds source mappings and mission metadata. `upload/` holds assembled draft packets when present. Independent read-backs in `audits/` accompany every draft item. The three goals have 26 supporting milestones in total. `sources.json` and `references.bib` provide the paper links and citations. `build-logs/verification.json` records the exact source hashes and compilation outcomes of the latest complete check; inspect its `success` and `all_modules_checked` fields before relying on it.

The pinned environment is Lean **4.33.1**, Mathlib **0df444a360eaa60ab8c11dca51a86af692955474**. Local dependency artifacts are reused through a machine-specific `.lake/packages` symlink. They are excluded from the portable archive. On a fresh machine, resolve the checked-in pin and fetch its cache:

```sh
lake update
lake exe cache get
python3 scripts/check_all.py
```

On the preparation machine, run `python3 scripts/check_all.py` directly. It invokes the installed Lean binary with cached import paths and writes compiled files locally. Definitions are checked separately; independent theorem statements with identical preambles share a compilation group. The report records each source hash and its compilation group. It does not ask Lake to rebuild the shared dependency cache. To check a single file, use `python3 scripts/lean_check.py Definitions/NAME.lean`.

## Draft upload

The uploader validates one canonical packet offline by default:

```sh
python3 scripts/stage_drafts.py upload/NAME.json
```

This mode makes no network requests and reads no credentials. A packet contains proposal metadata, ordered definition and theorem items, the goal's local key, supporting milestones, source citations, and independent read-backs. All draft definitions precede the theorem items that import them.

For an authorized upload, add `--write`. The packets carry the existing Theoretical Computer Science field UUID from a local platform snapshot; confirm live field availability or override with `--field-id UUID` when needed. The helper reads saved credentials from `~/prove2me_workspace/credentials.json`, checks that the live service offers the pinned environment, searches for library duplicates, and stages editable proposal items. Stage and launch the papers in the listed order. When a shared definition has already been published, the helper reuses an exactly identical library entry as a reference; different code stops staging for review. All staged proposals remain unpublished in `Draft` status. The `visibility` metadata describes the eventual mission; drafts are private regardless of that setting.

State files retain server IDs. If a write has an uncertain outcome, the helper stops and requires a read-only `--reconcile` before continuing. It has no endpoint for confirming items, submitting a proposal, launching a mission, accepting licensing terms, or publishing a theorem.

The [captain workflow](https://github.com/prove2me/prove2me_workspace/blob/main/references/mission_captain.md) reserves the final self-audit and **Submit Proposal** action for the human account holder. Review each definition, statement, and read-back before using that action.

## Platform upload status

The Cunningham mission was uploaded on 2026-11-02 and remains a private **Draft**, proposal `56809bca-587b-4681-a37e-5c1a6151675c`. Open [My missions](https://prove2.me/my-missions) and select **Exponential lower bounds for Cunningham’s rule**. Server readback verified all four definition modules, nine open theorem targets, eight milestones, the goal, order, and independent readbacks against the local packet. The [upload receipt](upload/cunningham.receipt.json) records this verification. Live environment and field availability were confirmed, and existing proposals and library entries were checked before creation.

The 16 proved audit certificates remain in the local bundle; the draft contains the mission statements and readbacks. Item confirmation and **Submit Proposal** remain the human account holder's website actions. The parity and Zadeh packets have not been uploaded.

During upload this environment's Python and child-process network calls could not resolve the host; direct approved curl tool calls succeeded. `stage_drafts.py --transport manual-curl` supports that tool-mediated execution while retaining temporary credential files, redirect refusal, sequential writes, and saved reconciliation state. Ordinary hosts can use the default transport or `--transport curl`. Temporary authentication files were removed after final verification.

Run `python3 scripts/make_archive.py` after completing verification and assembling the packets to refresh the portable file manifest and `friedmann-missions.zip`.

## Source interpretation points for review

The [Cunningham source audit](notes/cunningham-audit-summary.txt) is complete. Independent source and semantic reviews justify the three boundary reward contributions; a Lean certificate proves the local elimination and its connection to the actual coefficients for all size parameters. The review also corrected an erroneous claim about the alternative initial policy and added boundedness directly to cube realization. The package follows the graph-derived LP and explicit counter start, with the source's conflicting shorthand recorded. Its nine research targets remain open, and the rational-to-real geometry bridge is documented mathematically rather than proved in Lean.

The Zadeh package retains deterministic reward vertices and states the comparison between its concrete tie rule and the source transition convention as a separate target. Both repeated-priority constructions use priority occurrence counts. Exact exploratory runs and source crosswalks are in `notes/`; finite checks do not prove the research targets. The deterministic mission states existential hard families and requires witnesses and their linear edge bounds to be proved.

## Requested Google Cloud workers

The two-worker provisioning setup is in [cloud/README.md](cloud/README.md). VM creation was blocked by DNS access to the Google Cloud API, so no VMs are claimed to exist. The scripts and startup configuration are prepared and syntax checked.
