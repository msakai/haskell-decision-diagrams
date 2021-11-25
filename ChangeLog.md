# Changelog for `decision-diagrams` package

## 0.2.0.0

### Changes

* Make `Leaf :: Bool -> BDD a` as a basic constructor instead of
  `F`/`T` (in case of BDD) and `Empty`/`Base` (in case of ZDD), and
  remove `F`/`T`.

* `ZDD.toList` now returns sorted list

* Change signature of `fold` and `fold'` of BDD
  * Before: `b -> b -> (Int -> b -> b -> b) -> BDD a -> b`
  * After: `(Int -> b -> b -> b) -> (Bool -> b) -> BDD a -> b`

* Change signature of `fold` and `fold'` of ZDD (ditto)

* Add `HasCallStack` to some functions that are expected to raise excpetions

### Additions

* Introduce signature functor type (`Sig`)

* Add new operations:
  * BDD:
    * fixed point operators `lfp` and `gfp`
    * satisfiability related functions: `anySat`, `allSat`, `anySatComplete`, `allSatComplete`, `countSat`, `uniformSatM`
	* pseudo-boolean constraint functions: `pbAtLeast`, `pbAtMost`, `pbExactly`, `pbExactlyIntegral`
  * ZDD:
    * `combinations`
	* pseudo-boolean constraint functions: `subsetsAtLeast`, `subsetsAtMost`, `subsetsExactly`, `subsetsExactlyIntegral`
  * Both BDD and ZDD
    * `numNodes`
    * `unfoldHashable` and `unfoldOrd`

### Bug fixes

* Fix laziness of `fold` and `fold'`

### Other changes

* Introduced `doctest`

* Add other-extensions fields to `package.yaml`
