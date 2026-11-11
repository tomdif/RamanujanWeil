# Theta/Jacobian model: current reduction

The public entry point is
`RamanujanWeil.Arith.Deuring.Geom.G7.ThetaJ.thetaJacobianModel_of_gaps`.
It proves `ThetaJacobianModel K` from five explicit propositions. This remains
a conditional theorem; splitting a hypothesis does not prove its inputs.

## Proved components

- `DeuringG7ThetaJTwist.lean` constructs the semilinear Frobenius twist on the
  quotient surface (`exists_twist`).
- `DeuringG7ThetaJProd.lean` supplies the product branch
  (`prodJacModel_of_prodIso`), given the product decomposition and the stated
  Frobenius compatibility.
- `DeuringG7ThetaJ.lean` derives endomorphism compatibility from centrality and
  the epimorphism property (`frobDefined_of_central`), and assembles the branches.

## Remaining inputs

| Proposition | Mathematical obligation |
|---|---|
| `ThetaDichotomy K` | A principally polarized surface in this setting has a smooth genus-2 theta curve or splits as a product of elliptic curves |
| `ThetaFrobStable K` | A theta curve has a Frobenius-stable translate under the stated compatibility assumptions |
| `ThetaAlbanese K` | The theta curve's Jacobian is the surface, compatibly with Frobenius |
| `FrobeniusCentral K` | The quotient Frobenius commutes with every group endomorphism in the ordinary setting |
| `AbsFrobEpi K` | Absolute Frobenius on the abelian variety is an epimorphism of schemes |

Exact quantifiers and hypotheses are in
[DeuringG7ThetaJ](../RamanujanWeil/Arith/DeuringG7ThetaJ.lean).
The genus-2 descent obligation is separate: `Genus2FrobCanonical` is reduced to
`Genus2PresRigid` by
[DeuringG7G2Desc2Canon](../RamanujanWeil/Arith/DeuringG7G2Desc2Canon.lean), and
`Genus2FixedDescent` is still needed. Together these supply the inputs of
[principal finiteness](ARITH_DEURING_G7_PRINCIPAL.md).

## Verification

```sh
lake build RamanujanWeil.Arith.DeuringG7ThetaJAxioms
lake build RamanujanWeil.Arith.DeuringG7G2Desc2CanonAxioms
```

The respective audits contain 12 and 6 declarations. Their expected dependencies
are a subset of `propext`, `Classical.choice`, and `Quot.sound`.
See [publication verification](verification/publication_2026_11_11.json) for
the build results and source hashes.
