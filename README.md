# Elligator

This project formalizes the Elligator theory as presented in
[Elligator: Elliptic-curve points indistinguishable from uniform random strings](https://elligator.cr.yp.to/elligator-20130828.pdf)
by Daniel J. Bernstein, Mike Hamburg, Anna Krasnova, and Tanja Lange.

## Translation

```
├── Basic.lean
├── Elligator1                                 -- Chapter 3 and 4
│   ├── AuxiliaryCoordinates.lean              -- Theorem 1 facts about `u`, `v`, `X`, `Y` 
│   ├── Curve1174.lean                         -- Chapter 4
│   ├── CurveParameters.lean                   -- Theorem 1 facts about `c`, `r`, `d`
│   ├── EdwardsCurve.lean                      
│   ├── Example.lean                           -- Showcase of Elligator 1 usage
│   ├── InvertedMap.lean                       -- Theorem 3
│   ├── Map.lean                               -- Theorem 1 and Definition 2
│   ├── OutputCoordinates.lean                 -- Theorem 1 facts about `x`, `y`
│   ├── PhiOverFCharacterization.lean
│   ├── ReconstructionCoordinates.lean         -- Theorem 3 proof part A
│   ├── ReverseProofVehicle.lean               -- Theorem 3 proof part C
│   ├── StringEncoding.lean                    -- Theorem 4
│   └── XbarConsequences.lean
├── FiniteFieldBasic.lean
├── LegendreSymbol.lean
└── Primitives
    ├── ECC
    │   ├── Curves
    │   │   ├── Curve1174.lean
    │   │   └── Curve1174Prime.lean
    │   └── EdwardsCurve.lean
    └── PrimalityCertificate.lean
```

