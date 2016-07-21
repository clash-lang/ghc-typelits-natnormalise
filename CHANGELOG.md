# Changelog for the [`ghc-typelits-natnormalise`](http://hackage.haskell.org/package/ghc-typelits-natnormalise) package

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
