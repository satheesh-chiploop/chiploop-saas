# Limited MBIST Test Plan

- Scope: demo scratchpad memory only
- Algorithm: March C-
- Fault classes demonstrated: stuck-at, transition-like read/write checks
- Open-source status: generated RTL collateral and simulation-ready intent only
- Production DFT note: MBIST insertion, repair, redundancy, fuse programming, and signoff coverage should use customer DFT tools through ChipLoop private adapters.

## Sequence

1. Write 0 ascending addresses.
2. Read 0 and write 1 ascending addresses.
3. Read 1 and write 0 descending addresses.
4. Read 0 descending addresses.
5. Report fail on first observed mismatch.
