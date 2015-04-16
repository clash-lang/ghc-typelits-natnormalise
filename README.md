# ghc-tynat-normalise

[![Build Status](https://secure.travis-ci.org/christiaanb/ghc-typelits-natnormalise.png?branch=master)](http://travis-ci.org/christiaanb/ghc-typelits-natnormalise)

A type checker plugin for GHC that can solve _equalities_ 
of types of kind `Nat`, where these types are either:

* Type-level naturals
* Type variables
* Applications of the arithmetic expressions `(+,-,*,^)`.

It solves these equalities by normalising them to _sort-of_
`SOP` (Sum-of-Products) form, and then perform a
simple syntactic equality.

For example, this solver can prove the equality between:

```
(x + 2)^(y + 2)
```

and

```
4*x*(2 + x)^y + 4*(2 + x)^y + (2 + x)^y*x^2
```

Because the latter is actually the `SOP` normal form
of the former.

To use the plugin, add

```
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
```

To the header of your file.
