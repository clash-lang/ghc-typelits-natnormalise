# Changelog for the [`ghc-typelits-natnormalise`](http://hackage.haskell.org/package/ghc-typelits-natnormalise) package

## Unreleased
* Fix `n <= 0` constrained being reported as impossible.

## 0.7.10 *May 22nd 2024*
* Support for GHC 9.10.1

## 0.7.9 *October 10th 2023*
* Support for GHC 9.8.1

## 0.7.8 *February 20th 2023*
* Try and outright solve substituted constraints, the same as is done with the unsubstituted constraint. Partially Fixes [#65](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/65).
* Support for GHC-9.6.0.20230210

## 0.7.7 *October 10th 2022*
* Solve unflattened wanteds instead of the wanteds passed to the plugin. Fixes [#1901]https://github.com/clash-lang/clash-compiler/issues/1901.
* Add support for GHC 9.4

## 0.7.6 *June 20th 2021*
* Do not vacuously solve `forall a b . 1 <=? a^b ~ True`
* Do not solve constraints within `KnownNat`, leave that to https://hackage.haskell.org/package/ghc-typelits-knonwnnat

## 0.7.5 *June 17th 2021*
* Fixes [#52](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/50) Plugin doesn't solve inside arbitrary class constraints
* Build on GHC 9.2.0.20210422

## 0.7.4 *February 12th 2021*
* Fixes [#50](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/50) `x ^ C ~ y` erroneously deemed hard insoluable, a contradiction, when `C` is some type family other than +,-,*,^

## 0.7.3 *January 1st 2021*
* Build on GHC 9.0.1-rc1

## 0.7.2 *March 9 2020*
* Fixes [#44](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/44) infinite loop due to boxed equality

## 0.7.1 *February 6th 2020*
* Add support for GHC 8.10.1-alpha2
* Fixes [#23](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/23): Can't figure out `+` commutes in some contexts on GHC 8.6.3
* Fixes [#28](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/28): Using the solver seems to break GHC
* Fixes [#34](https://github.com/clash-lang/ghc-typelits-natnormalise/issues/34): inequality solver mishandles subtraction

## 0.7 *August 26th 2019*
* Require KnownNat constraints when solving with constants

## 0.6.2 *July 10th 2018*
* Add support for GHC 8.6.1-alpha1
* Solve larger inequalities from smaller inequalities, e.g.
  * `a <= n` implies `a <= n + 1`

## 0.6.1 *May 9th 2018*
* Stop solving `x + y ~ a + b` by asking GHC to solve `x ~ a` and `y ~ b` as
  this leads to a situation where we find a solution that is not the most
  general.
* Stop using the smallest solution to an inequality to solve an equality, as
  this leads to finding solutions that are not the most general.
* Solve smaller inequalities from larger inequalities, e.g.
  * `1 <= 2*x` implies `1 <= x`
  * `x + 2 <= y` implies `x <= y` and `2 <= y`

## 0.6 *April 23rd 2018*
* Solving constraints with `a-b` will emit `b <= a` constraints. e.g. solving
  `n-1+1 ~ n` will emit a `1 <= n` constraint.
  * If you need subtraction to be treated as addition with a negated operarand
    run with `-fplugin-opt GHC.TypeLits.Normalise:allow-negated-numbers`, and
    the `b <= a` constraint won't be emitted. Note that doing so can lead to
    unsound behaviour.
* Try to solve equalities using smallest solution of inequalities:
  * Solve `x + 1 ~ y` using `1 <= y` => `x + 1 ~ 1` => `x ~ 0`
* Solve inequalities using simple transitivity rules:
  * `2 <= x` implies `1 <= x`
  * `x <= 9` implies `x <= 10`
* Solve inequalities using _simple_ monotonicity of addition rules:
  * `2 <= x` implies `2 + 2*x <= 3*x`
* Solve inequalities using _simple_ monotonicity of multiplication rules:
  * `1 <= x` implies `1 <= 3*x`
* Solve inequalities using _simple_ monotonicity of exponentiation rules:
  * `1 <= x` implies `2 <= 2^x`
* Solve inequalities using powers of 2 and monotonicity of exponentiation:
  * `2 <= x` implies `2^(2 + 2*x) <= 2^(3*x)`

## 0.5.10 *April 15th 2018*
* Add support for GHC 8.5.20180306

## 0.5.9 *March 17th 2018*
* Add support for GHC 8.4.1

## 0.5.8 *January 4th 2018*
* Add support for GHC 8.4.1-alpha1

## 0.5.7 *November 7th 2017*
* Solve inequalities such as: `1 <= a + 3`

## 0.5.6 *October 31st 2017*
* Fixes bugs:
  * `(x + 1) ~ (2 * y)` no longer implies `((2 * (y - 1)) + 1) ~ x`

## 0.5.5 *October 22nd 2017*
* Solve inequalities when their normal forms are the same, i.e.
  * `(2 <= (2 ^ (n + d)))` implies `(2 <= (2 ^ (d + n)))`
* Find more unifications:
  * `8^x - 2*4^x ~ 8^y - 2*4^y ==> [x := y]`

## 0.5.4 *October 14th 2017*
* Perform normalisations such as: `2^x * 4^x ==> 8^x`

## 0.5.3 *May 15th 2017*
* Add support for GHC 8.2

## 0.5.2 *January 15th 2017*
* Fixes bugs:
  * Reification from SOP to Type sometimes loses product terms

## 0.5.1 *September 29th 2016*
* Fixes bugs:
  * Cannot solve an equality for the second time in a definition group

## 0.5 *August 17th 2016*
* Solve simple inequalities, i.e.:
  * `a  <= a + 1`
  * `2a <= 3a`
  * `1  <= a^b`

## 0.4.6 *July 21th 2016*
* Reduce "x^(-y) * x^y" to 1
* Fixes bugs:
  * Subtraction in exponent induces infinite loop

## 0.4.5 *July 20th 2016*
* Fixes bugs:
  * Reifying negative exponent causes GHC panic

## 0.4.4 *July 19th 2016*
* Fixes bugs:
  * Rounding error in `logBase` calculation

## 0.4.3 *July 18th 2016*
* Fixes bugs:
  * False positive: "f :: (CLog 2 (2 ^ n) ~ n, (1 <=? n) ~ True) => Proxy n -> Proxy (n+d)"

## 0.4.2 *July 8th 2016*
* Find more unifications:
  * `(2*e ^ d) ~ (2*e*a*c) ==> [a*c := 2*e ^ (d-1)]`
  * `a^d * a^e ~ a^c ==> [c := d + e]`
  * `x+5 ~ y ==> [x := y - 5]`, but only when `x+5 ~ y` is a given constraint

## 0.4.1 *February 4th 2016*
* Find more unifications:
  * `F x y k z ~ F x y (k-1+1) z` ==> [k := k], where `F` can be any type function

## 0.4 *January 19th 2016*
* Stop using 'provenance' hack to create conditional evidence (GHC 8.0+ only)
* Find more unifications:
  * `F x + 2 - 1 - 1 ~ F x` ==> [F x := F x], where `F` can be any type function with result `Nat`.

## 0.3.2
* Find more unifications:
  * `(z ^ a) ~ (z ^ b) ==> [a := b]`
  * `(i ^ a) ~ j ==> [a := round (logBase i j)]`, when `i` and `j` are integers, and `ceiling (logBase i j) == floor (logBase i j)`.

## 0.3.1 *October 19th 2015*
* Find more unifications:
  * `(i * a) ~ j ==> [a := div j i]`, when `i` and `j` are integers, and `mod j i == 0`.
  * `(i * a) + j ~ k  ==> [a := div (k-j) i]`, when `i`, `j`, and `k` are integers, and `k-j >= 0` and `mod (k-j) i == 0`.

## 0.3 *June 3rd 2015*
* Find more unifications:
  * `<TyApp xs> + x ~ 2 + x ==> [<TyApp xs> ~ 2]`
* Fixes bugs:
  * Unifying `a*b ~ b` now returns `[a ~ 1]`; before it erroneously returned `[a ~ ]`, which is interpred as `[a ~ 0]`...
  * Unifying `a+b ~ b` now returns `[a ~ 0]`; before it returned the undesirable, though equal, `[a ~ ]`

## 0.2.1 *May 6th 2015*
* Update `Eq` instance of `SOP`: Empty SOP is equal to 0

## 0.2 *April 22nd 2015*
* Finds more unifications:
  * `(2 + a) ~ 5  ==>  [a := 3]`
  * `(3 * a) ~ 0  ==>  [a := 0]`

## 0.1.2 *April 21st 2015*
* Don't simplify expressions with negative exponents

## 0.1.1 *April 17th 2015*
* Add workaround for https://ghc.haskell.org/trac/ghc/ticket/10301

## 0.1 *March 30th 2015*
* Initial release
