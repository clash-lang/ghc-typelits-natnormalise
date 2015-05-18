# Changelog for the [`ghc-typelits-natnormalise`](http://hackage.haskell.org/package/ghc-typelits-natnormalise) package

## 0.2.2
* Find more unifications:
  * `<TyApp xs> + x ~ 2 + x` ==> [<TyApp xs> ~ 2]

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
