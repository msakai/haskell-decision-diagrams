# decision-diagrams

Hackage:
[![Hackage](https://img.shields.io/hackage/v/decision-diagrams.svg)](https://hackage.haskell.org/package/decision-diagrams)
[![Hackage Deps](https://img.shields.io/hackage-deps/v/decision-diagrams.svg)](https://packdeps.haskellers.com/feed?needle=decision-diagrams)
[![Hackage CI](https://matrix.hackage.haskell.org/api/v2/packages/decision-diagrams/badge)](https://matrix.hackage.haskell.org/#/package/decision-diagrams)

Dev:
[![Build Status](https://github.com/msakai/haskell-decision-diagrams/actions/workflows/build.yaml/badge.svg)](https://github.com/msakai/haskell-decision-diagrams/actions/workflows/build.yaml)
[![Coverage Status](https://coveralls.io/repos/msakai/haskell-decision-diagrams/badge.svg)](https://coveralls.io/r/msakai/haskell-decision-diagrams)

Binary Decision Diagrams (BDD) and Zero-suppressed Binary Decision Diagrams (ZDD) implementation in Haskell.

Hash-consing is implemented using [intern](https://hackage.haskell.org/package/intern) package.

## Comparison with other BDD packages

|Package name|Repository|BDD|ZDD|Style|Implementation|Hash-consing / Fast equality test|
|------------|----------|---|---|-----|--------------|---------------------------------|
|[decision-diagrams](https://hackage.haskell.org/package/decision-diagrams) (this package)|[GitHub](https://github.com/msakai/haskell-decision-diagrams/)|✔️|✔️|pure|pure Haskell|✔️|
|[zsdd](https://hackage.haskell.org/package/zsdd)|[GitHub](https://github.com/eddiejones2108/decision-diagrams) (deleted?)|✔️|✔️|monadic|pure Haskell|✔️|
|[obdd](https://hackage.haskell.org/package/obdd)|[GitHub](https://github.com/jwaldmann/haskell-obdd)|✔️|-|pure|pure Haskell|-|
|[HasCacBDD](https://hackage.haskell.org/package/HasCacBDD)|[GitHub](https://github.com/m4lvin/HasCacBDD)|✔️|-|pure|FFI|✔️|
|[hBDD](https://hackage.haskell.org/package/hBDD) ([hBDD-CUDD](https://hackage.haskell.org/package/hBDD-CUDD), [hBDD-CMUBDD](https://hackage.haskell.org/package/hBDD-CMUBDD))|[GitHub](https://github.com/peteg/hBDD)|✔️|-|pure|FFI|✔️|

Please feel free to make a pull request for addition or correction.
