# decision-diagrams

Hackage:
[![Hackage](https://img.shields.io/hackage/v/decision-diagrams.svg)](https://hackage.haskell.org/package/decision-diagrams)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/decision-diagrams.svg)](https://packdeps.haskellers.com/feed?needle=decision-diagrams)
[![Hackage CI](https://matrix.hackage.haskell.org/api/v2/packages/decision-diagrams/badge)](https://matrix.hackage.haskell.org/#/package/decision-diagrams)

Dev:
[![Build Status](https://github.com/msakai/haskell-decision-diagrams/actions/workflows/build.yaml/badge.svg)](https://github.com/msakai/haskell-decision-diagrams/actions/workflows/build.yaml)
[![Coverage Status](https://coveralls.io/repos/msakai/haskell-decision-diagrams/badge.svg)](https://coveralls.io/r/msakai/haskell-decision-diagrams)

[Binary Decision Diagrams (BDD)](https://en.wikipedia.org/wiki/Binary_decision_diagram) and [Zero-suppressed Binary Decision Diagrams (ZDD)](https://en.wikipedia.org/wiki/Zero-suppressed_decision_diagram) implementation in Haskell.

BDD is a data stucture suitable for representing boolean functions (can be thought as a compressed representation of truth tables) and many operations on boolean functions can be performed efficiently.  ZDD is a variant of BDD suitable for representing (sparse) families of sets compactly.

BDD/ZDD uses hash-consing for compact representation and efficient comparison, and we use [intern](https://hackage.haskell.org/package/intern) package for implementing hash-consing.

## Comparison with other BDD packages for Haskell

|Package name|Repository|BDD|ZDD|Style|Implementation|Hash-consing / Fast equality test|Dynamic variable reordering|
|------------|----------|---|---|-----|--------------|---------------------------------|---------------------------|
|[decision-diagrams](https://hackage.haskell.org/package/decision-diagrams) (this package)|[GitHub](https://github.com/msakai/haskell-decision-diagrams/)|✔️|✔️|pure|pure Haskell|✔️|-|
|[zsdd](https://hackage.haskell.org/package/zsdd)|[GitHub](https://github.com/eddiejones2108/decision-diagrams) (deleted?)|✔️|✔️|monadic|pure Haskell|✔️|-|
|[obdd](https://hackage.haskell.org/package/obdd)|[GitHub](https://github.com/jwaldmann/haskell-obdd)|✔️|-|pure|pure Haskell|-|-|
|[HasCacBDD](https://hackage.haskell.org/package/HasCacBDD)|[GitHub](https://github.com/m4lvin/HasCacBDD)|✔️|-|pure|FFI|✔️|-|
|[hBDD](https://hackage.haskell.org/package/hBDD) ([hBDD-CUDD](https://hackage.haskell.org/package/hBDD-CUDD), [hBDD-CMUBDD](https://hackage.haskell.org/package/hBDD-CMUBDD))|[GitHub](https://github.com/peteg/hBDD)|✔️|-|pure|FFI|✔️|✔️|
|[cudd](https://hackage.haskell.org/package/cudd)|[GitHub](https://github.com/adamwalker/haskell_cudd)|✔️|-|both pure\*1 and monadic|FFI|✔️|✔️|

\*1: `cudd`'s pure interface is different from normal Haskell data types (like ones in the [containers](https://hackage.haskell.org/package/containers) package, for example) because it requires `DDManager` argument.

Please feel free to make a pull request for addition or correction to the comparision.
