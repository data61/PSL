# Translations
## Finite Mapping

- Problem: There is no equivalent to `FDOM`, `DRESTRICT`, ... for functions in Isabelle/HOL
- Solution: 
    + use `fmap` of `Finite_Map.thy` for states (state domain is finite variable set)
    + restrict theory to finite problems where necessary

## Implication Lemmas
### Premise Rewriting for ISAR Proofs
Lemmas of the form
```ML
    P1 /\ ... /\ Pn ==> C
```
need to be rewritten to standardized form
```ML
    P1 ==> ... ==> Pn ==> C
```
to be properly recognized in an ISAR proof:
```ML
    proof -
        assume P1 <P1>
        ...
        assume Pn <Pn>
        show <C> <proof>
    qed
```

> **Note:**
>
> Otherwise the error "failed refine pending goal" will occur.