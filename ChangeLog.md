# Changelog for decision-diagrams

## 0.2.0 (unreleased)

* `BDD`'s data constructors `F` and `T` are replaced with `Leaf`, and
  similarly `Node`'s data constructors `NodeF` and `NodeT` are
  replaced with `NodeLeaf`.

* Introduce signature functor types (`Sig`)

* Add other-extensions fields to `package.yaml`

* Add fixed point operators `BDD.lfp` and `BDD.gfp`

* Add `unfoldHashable` and `unfoldOrd` to BDD and ZDD

* Add `ZDD.combinations`

* Add pseudo-boolean constraint functions to BDD and ZDD

* Add satisfiability related functions to BDD

* Add `BDD.numNodes` and `ZDD.numNodes`

* `ZDD.toList` now returns sorted list

* Introduced `doctest`

* Fix laziness of `fold` and `fold'`

