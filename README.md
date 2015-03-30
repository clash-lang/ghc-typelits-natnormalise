# ghc-tynat-normalise

A type checker plugin for GHC that can solve /equalities/ of types of kind
'GHC.TypeLits.Nat', where these types are either:

* Type-level naturals
* Type variables
* Applications of the arithmetic expressions @(+,-,*,^)@.

It solves these equalities by normalising them to /sort-of/
'GHC.TypeLits.Normalise.SOP.SOP' (Sum-of-Products) form, and then perform a
simple syntactic equality.

For example, this solver can prove the equality between:

```
(x + 2)^(y + 2)
```

and

```
4*x*(2 + x)^y + 4*(2 + x)^y + (2 + x)^y*x^2
```

Because the latter is actually the 'GHC.TypeLits.Normalise.SOP.SOP' normal form
of the former.

To use the plugin, add

```
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
```

To the header of your file.
