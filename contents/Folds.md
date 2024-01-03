```{.haskell .invisible}
{-# LANGUAGE TypeOperators #-}
module Chapters.Folds where

import Prelude ()
import Control.Arrow ((***))
import Common.MiniPrelude hiding (exp, gcd)

import Chapters.Basics (square, ETree(..), ITree(..), positions, fork)
import Chapters.Derivation (steep, steepsum)
```

# 摺 {#ch:fold}
\index{fold 摺}

第\@ref{ch:induction}章中的許多歸納函數定義都循著同一個固定模式。
以 |sum|, |length|, 與 |map f| 為例：
```spec
sum :: List Int -> Int
sum []      = {-"{\color{burntorange}"-}0{-"}"-}
sum (x:xs)  = {-"{\color{burntorange}"-}x{-"\,"-} +{-"}\,"-} sum xs {-"~~,"-}

length :: List a -> Nat
length []      = {-"{\color{burntorange}"-}Zero{-"}"-}
length (x:xs)  = {-"{\color{burntorange}"-}Suc{-"}"-} (length xs) {-"~~,"-}

map :: (a -> b) -> List a -> List b
map f []      = {-"{\color{burntorange}"-}[]{-"}"-}
map f (x:xs)  = {-"{\color{burntorange}"-}f x{-"\,"-} :{-"\,}"-} map f xs {-"~~."-}
```
{.nobreak}它們都在輸入為 |[]| 時傳回某個基底值，在輸入為 |x:xs| 時在 |xs| 上遞迴呼叫，
並將呼叫結果稍作加工。
三者的不同之處只在橘色的部分，即基底值以及用於加工的函數：|sum| 使用 |0| 與 |(+)|, |length| 使用 |Zero| 與 |Suc|, |map f| 則使用 |[]| 與 |(f x :)|.
如果說「抽象化」是一個高階程式語言給我們的最重要能力，我們能否將這個模式抽象出來呢？

我們把上述三個定義中橘色的部分抽出變成參數，將餘下的函數稱為 |foldr|:
```spec
foldr :: (a -> b -> b) -> b -> List a -> b
foldr f e []      = e
foldr f e (x:xs)  = f x (foldr f e xs) {-"~~."-}
```
{.nobreak}如此一來，|sum|, |length|, 與 |map f| 都是 |foldr| 的特例：
```spec
sum     = foldr (+) 0 {-"~~,"-}
length  = foldr (\x n -> Suc n) Zero {-"~~,"-}
map f   = foldr (\x ys -> f x : ys) [] {-"~~."-}
```
{.nobreak}函數 |foldr| 是串列上的「摺(fold)」 --- |foldr| 一詞是 fold 與「右邊(right)」的縮寫，意謂該函數是一個往右結合的摺。我們將在下一節解釋。

## 串列的摺 {#sec:folds-on-lists}

「摺」有許多方式可理解。
我們可說 |foldr| 捕捉了最常見的一種歸納定義模式，並將它形式化地表達出來。
在第\@ref{ch:induction}章中，許多函數定義都遵循這樣的模式：
```spec
h :: List a -> b
h []      = e
h (x:xs)  = ... x ... h xs ...
```
{.nobreak}在 |h []| 的情況傳回某個基底值；在 |h (x:xs)| 的情況中可使用 |x| 與 |h xs| 的值。
如果上述定義中 |...| 之處*沒有出現 |xs|*, 則 |h| 的定義就能寫成一個 |foldr|.

我們也可將 |foldr| 視為組件(combinator)函數之一。\index{combinator 組件}
第\@ref{sec:list-combinators}節之中介紹了組件函數的觀念：
如同 |map|, |take|, |drop|, |zip| 等等的組件函數捕捉了常見的程式設計模式。
每個組件負責一項單一、通用、易重用的功能。
函數 |foldr| 也可視為一個組件，只是它比一些其他組件更抽象、更通用 --- 我們稍後將發現許多我們見過的組件函數都是 |foldr| 的特例。

還有一個理解 |foldr| 的方式：|foldr| 替換了串列中的建構元。
回顧：任何有限長度的串列都是由 |[]| 開始，有限次地套用 |(:)| 而來。
例如 |[x0,x1,x2]| 是 |x0 : (x1 : (x2 : []))| 的簡寫。
考慮 |foldr oplus e [x0,x1,x2]|:
```spec
     foldr oplus e (x0 : (x1 : (x2 : [])))
===  x0 `oplus` foldr oplus e (x1 : (x2 : []))
===  x0 `oplus` (x1 `oplus` foldr oplus e (x2 : []))
===  x0 `oplus` (x1 `oplus` (x2 `oplus` foldr oplus e []))
===  x0 `oplus` (x1 `oplus` (x2 `oplus` e)) {-"~~."-}
```
{.nobreak}我們可看到 |foldr| 將串列走訪一次，將每個 |(:)| 替換成 |oplus|, 將 |[]| 替換成 |e|.
式子中的括號往右邊結合，這是 |foldr| 的名字中字母 |r| 的由來。
這種理解也便於解釋 |foldr| 的型別。
回想串列的兩個建構元，

  * |[]| 的型別是 |List a|,
  * |(:)| 的型別是 |a -> List a -> List a|.

{.nobreak}函數 |foldr oplus e| 接收一個 |List a|，把其中的建構元分別替換為 |e| 與 |oplus|，藉此算出一個型別為 |b| 的值。因此，

  * |e| 是輸入為 |[]| 時立刻傳回的值，其型別必須是 |b|.
  * 至於 |oplus| 的型別，考慮 |x0 `oplus` (x1 `oplus` (x2 `oplus` e))| 這個式子。
    其中 |x0| 的型別為 |a|, |x1 `oplus` (x2 `oplus` e)| 是建構元已被替換過的串列，型別應該為 |b|.
    而 |oplus| 拿到這兩個輸入後，得算出一個型別為 |b| 的值.
    因此 |oplus| 的型別為 |a -> b -> b|.

{.nobreak}注意：|e| 與 |oplus| 的型別分別是將 |[]| 與 |(:)| 的型別中的 |List a| 代換成 |b| 而來。
綜合言之，
|foldr| 的型別是 |(a -> b -> b) -> b -> List a -> b|.

為方便說明，此後我們將 |foldr oplus e| 之中的 |e| 稱作*基底值*(*base value*)\index{fold 摺!base value 基底值}，將 |oplus| 稱作*步驟函數*(*step function*)\index{fold 摺!step function 步驟函數}.
函數 |foldr| 的型別可以理解為：給一個型別為 |a -> b -> b| 的步驟函數，和一個型別為 |b| 的基底值，|foldr| 就能將一個 |List a| 轉換為 |b|.

串列的摺(|foldr|)只是一個常用的特例 ---「將資料結構中的建構元代換掉」的動作也可推廣到其他資料結構上。
我們在之後的章節中將看到一些其他資料結構上的摺。

下一節將舉更多使用 |foldr| 的例子。
在那之前我們再次提醒讀者：在 |foldr oplus e (x:xs)| 的狀況中，|oplus| 可以使用 |x| 與 |foldr oplus e xs| 的結果，但不能直接使用 |xs|.

### 更多串列上的摺 {#sec:more-folds-on-lists}

回顧起來，我們可發現第\@ref{ch:induction}章介紹的許多函數都是 |foldr|.
:::{.example #eg:foldr}
以下函數都可寫成 |foldr|:

  * |concat = foldr (++) []|.
  * |filter p = foldr (\ x xs -> if p x then x:xs else xs) []|,
  * |takeWhile p = foldr (\x xs -> if p x then x:xs else []) []|,
  * |elem x = foldr (\y b -> x == y |||| b) False|,
  * |all p = foldr (\x b -> p x && b) True|.


:::

串列連接 |(++) :: List a -> List a -> List a| 雖是個二元運算，
若將 |(++ ys) :: List a -> List a| 視為一個函數，它可寫成一個 |foldr|:
```spec
 (++ ys) = foldr (:) ys {-"~~."-}
```
{.nobreak}一個重要的特例是當 |ys = []| 時。對任何 |xs|, |xs ++ [] = xs|. 因此 |(++[])| 是串列上的 |id|:
```spec
id :: List a -> List a
id = foldr (:) [] {-"~~."-}
```
{.nobreak}確實，將一個串列中的 |(:)| 代換成 |(:)|, |[]| 代換成 |[]|, 我們還是得到原來的串列。
我們日後還會用到「串列上的 |id| 是一個 |foldr|」的性質。

計算所有前段的函數 |inits :: List a -> List (List a)| 可寫成 |foldr|:
\index{list 串列!prefix 前段}
```haskell
inits = foldr (\x xss -> [] : map (x:) xss) [[]] {-"~~."-}
```
{.nobreak}計算所有後段的 |tails :: List a -> List (List a)| 也可以寫成 |foldr|，但需要用一個小性質。
回顧其定義：
\index{list 串列!suffix 後段}
```spec
tails []      = [[]]
tails (x:xs)  = (x:xs) : tails xs {-"~~."-}
```
{.nobreak}乍看之下這不符合 |foldr| 的模式：參數 |xs| 出現在 |... : tails xs| 的左邊，但在 |foldr| 的模式中，|xs| 不能出現在遞迴呼叫之外。
幸好 |tails| 有一個剛好在此有用的小特性：|tails xs| 傳回的所有後段中，第一個就是 |xs| 本身：|head (tails xs) = xs|.
因此我們可將 |tails| 寫成：
```haskell
tails = foldr (\x xss -> (x : head xss) : xss) [[]] {-"~~."-}
```
{.nobreak}由於 |tails| 永遠傳回非空串列，使用 |head xss| 是安全的。

:::{.exlist}
:::{.exer #ex:perms-sublists-splits-foldr}
請將以下函數寫成 |foldr|:

  1. |perms :: List a -> List (List a)| (見第\@ref{sec:fan-perm}節),
  2. |sublists :: List a -> List (List a)| (見第\@ref{sec:fan-perm}節),
  3. |splits :: List a -> List (List a :* List a)| （見習題\@ref{ex:splits}）。



:::
:::{.exans .compact}

  1. |perms = foldr (\x xss -> concat (map (fan x) xss)) [[]]|
  2. |sublists = foldr (\x xss -> xss ++ map (x:) xss) [[]]|
  3. |splits| 可定義如下：

```haskell
splits = foldr spl [([],[])] {-"~~,"-}
  where  spl x ((xs,ys):zss) =
           ([],x:xs++ys) : map ((x:) *** id) ((xs,ys):zss) {-"~~."-}
```

:::
:::

### 不是 |foldr| 的函數 {#sec:not-foldr}

並非所有輸入為串列的函數都是 |foldr|.
最明顯的例子是 |tail|: 我們無法由 |x| 和 |tail xs| 算出 |tail (x:xs)|。
例如，|tail [1,2,3] = [2,3]|，但 |tail [2,3] = [3]|, 而 |[2,3]| 無法由 |1| 和 |[3]| 組出來。

另一個例子是 |dropWhile p|. 回顧其定義：
```spec
dropWhile p []      = []
dropWhile p (x:xs)  = if p x then dropWhile p xs else x:xs {-"~~,"-}
```
{.nobreak}在歸納情況中，|else| 的分支需傳回 |x:xs| --- |xs| 出現在遞迴呼叫以外的地方。這樣的程式不是 |foldr|。
當然，這只表示 |dropWhile p| 的*這個*定義不符合 |foldr| 的模式.
是否有其他的方式能將 |dropWhile p| 寫成 |foldr| 呢？
不論 |dropWhile p| 是怎麼定義的，考慮
|dropWhile even [4,3,6,2] = [3,6,2]|, 但 |dropWhile even [3,6,2] = []| ---
看來，|dropWhile p| 丟掉了太多資訊，使得我們無法保證能從 |dropWhile p xs| 重組出 |dropWhile p (x:xs)|。
因此，|dropWhile p| 和 |tail| 一樣，是先天上無法寫成 |foldr| 的。

:::{.exlist}
:::{.exer #ex:fan-foldr}
考慮第\@ref{sec:fan-perm}節的函數 |fan|:
```spec
fan :: a -> List a -> List (List a)
fan y []      = [[y]]
fan y (x:xs)  = (y:x:xs) : map (x:) (fan y xs) {-"~~."-}
```
{.nobreak}為何這個定義目前的形式不是一個 |foldr|?
有沒有可能將 |fan y| 寫成一個 |foldr| 呢？
:::
:::{.exans}
由於 |xs| 出現在遞迴呼叫以外的地方 --- |((y:x:xs) :)|, 此處的 |fan| 定義並不是一個 |foldr|.
但由於 |tail (head (fan y xs)) = xs|
（例如，|fan 5 [1,2,3] = [[5,1,2,3],[1,5,2,3],[1,2,5,3],[1,2,3,5]]|,
因此 |tail (head (fan 5 [1,2,3])) = [1,2,3]|），
我們可將 |fan|寫成：
```texonly
%{
%format fan' = "\Varid{fan}"
```
```haskell
fan' y = foldr (\x xss -> (y:x: tail (head xss)) : map (x:) xss) [[y]] {-"~~."-}
```
```texonly
%} %fan'
```
:::
:::

## 摺融合定理 {#sec:foldr-fusion}

第\@ref{ch:intro}章中提及，「抽象化」意指抽取出我們認為重要的概念、成分，給予一個名字或符號。
如此一來，這個概念正式地「存在」了，我們可以談論它、研究其性質，並將研究結果應用在所有符合這個抽象概念的事物上。
一個程式語言最重要的功能之一是提供良好的抽象化機制。
由於高階函數等等性質，函數語言讓我們能較容易地對程式結構作抽象。

「摺」是我們找到的一個抽象，許多程式可以表達為摺。
而一旦辨識出了摺這個結構，我們可開始討論所有摺都滿足的性質，
這些性質則將可適用於所有是摺的程式上。

關於摺的性質中，最重要的也許是本節的*摺融合定理*(*fold-fusion theorem*)。

摺融合定理告訴我們一個摺如何能與串接於其後的函數融合起來，成為單獨的一個摺：
:::{.theorem title="摺融合定理(串列版)" #thm:foldr-fusion}
\index{fold 摺!fold fusion 摺融合}
給定 |f :: a -> b -> b|, |e :: b|, |h :: b -> c|.
如果 |h (f x y) = g x (h y)| 對所有 |x :: a| 與*在 |foldr f e| 的值域中的* |y :: b| 成立，則
```spec
h . foldr f e = foldr g (h e) {-"~~."-}
```
:::
性質 |h (f x y) = g x (h y)| 是該融合能成立的充分條件，我們日後將稱之為「*融合條件*(*fusion condition*)」。\index{fold 摺!fusion condition 融合條件}
如果定理本身看來太抽象，下述例子也許可給讀者一些直覺。考慮 |[x0,x1,x2]|:
```{.haskell .invisible}
foldrFusionEx :: (a -> b) -> (c -> a -> a) -> a -> (c -> b -> b) -> c -> c -> c -> b
foldrFusionEx h f e g x0 x1 x2 =
```
```haskell
      {-"{\color{burntorange}"-}h{-"}"-} (foldr f e [x0,x1,x2])
 ===    {- |foldr| 之定義 -}
      {-"{\color{burntorange}"-}h{-"}"-} (f x0 (f x1 (f x2 e)))
 ===    {- 融合條件: |{-"{\color{burntorange}"-}h{-"}"-} (f x y) = g x ({-"{\color{burntorange}"-}h{-"}"-} y)| -}
      g x0 ({-"{\color{burntorange}"-}h{-"}"-} (f x1 (f x2 e)))
 ===    {- 融合條件: |{-"{\color{burntorange}"-}h{-"}"-} (f x y) = g x ({-"{\color{burntorange}"-}h{-"}"-} y)| -}
      g x0 (g x1 ({-"{\color{burntorange}"-}h{-"}"-} (f x2 e)))
 ===    {- 融合條件: |{-"{\color{burntorange}"-}h{-"}"-} (f x y) = g x ({-"{\color{burntorange}"-}h{-"}"-} y)| -}
      g x0 (g x1 (g x2 ({-"{\color{burntorange}"-}h{-"}"-} e)))
 ===    {- |foldr| 之定義 -}
      foldr g ({-"{\color{burntorange}"-}h{-"}"-} e) [x0,x1,x2] {-"~~."-}
```
{.nobreak}由此例可看出融合條件 |h (f x y) = g x (h y)| 的作用 --- 將 |h| 往右推，並將途中經過的 |f| 都變成 |g|, 直到碰到 |e| 為止。

定理\@ref{thm:foldr-fusion}可用例行的歸納證明證成：
:::{.proof}
假設融合條件成立，我們需證明對所有 |xs|, |h (foldr f e xs) = foldr g (h e) xs|.

{.nobreak}**情況** |xs := []|:
```spec
      h (foldr f e [])
 ===  h e
 ===  foldr g (h e) [] {-"~~."-}
```

{.nobreak}**情況** |xs := x:xs|:
```spec
      h (foldr f e (x:xs))
 ===    {- |foldr| 之定義 -}
      h (f x (foldr f e xs))
 ===    {- 融合條件: |h (f x y) = g x (h y)| -}
      g x (h (foldr f e xs))
 ===    {- 歸納假設 -}
      g x (foldr g (h e) xs)
 ===    {- |foldr| 之定義 -}
      foldr g (h e) (x:xs) {-"~~."-}
```
:::

{title="註記" #para:bring-in-context-prelim}
我們在歸納情況的第二步使用了融合條件 |h (f x y) = g x (h y)|. 欲使該步成立，融合條件不須對所有 |y| 都成立 --- 我們只需要它在 *|y| 是 |foldr f e| 的可能結果*時成立即可。這是定理\@ref{thm:foldr-fusion}中「在 |foldr f e| 的值域中的 |y|」這句話的由來。\index{fold 摺!bringing in the context 引入脈絡}

在本章接下來大部分的例子中，我們其實可以證明融合條件對*所有 |y|* 均成立。但只要我們處理的演算法問題稍微複雜些，我們便會常遇到融合條件只對 |foldr f e| 的值域中的 |y| 成立的情況。
我們將在第\@ref{sec:bring-in-context}節中看到一些例子。

### 將摺融合用於定理證明 {#sec:foldr-fusion-theorem-proof}

定理\@ref{thm:foldr-fusion}有幾種用法：

  * 一種可能是用於證明性質：我們希望證明 |h . foldr f e| 與 |foldr g (h e)| 相等，此時我們已知 |h|, |f|, |g|, 與 |e|.
  * 另一種可能是用於生成程式。此時我們通常已知 |h|, |f|, 與 |e|, 但不知道 |g|. 我們希望找到一個讓融合條件成立的 |g|, 使得 |h . foldr f e| 能在一個 |foldr| 之中完成。

我們先討論第一種情況。
:::{.example #ex:map-fusion-foldr-fusion}
回顧 |map| 融合定理(\@ref{thm:map-fusion}): |map f . map g = map (f.g)|.
第 \@pageref{thm:map-fusion} 頁提供了一個歸納證明。
由於 |map g| 是一個摺，我們也可用摺融合定理證明如下。
```{.haskell .invisible}
mapFusionFuse0 :: (a -> b) -> (c -> a) -> List c -> List b
mapFusionFuse0 f g =
```
```haskell
      map f . map g
 ===   {- |map| 的摺定義 -}
      map f . foldr (\x ys -> g x : ys) []
 ===   {- 摺融合 -}
      foldr (\x ys -> f (g x) : ys) []
 ===   {- |map| 的摺定義 -}
      map (f . g) {-"~~."-}
```
{.nobreak}第二步需要的融合條件只需簡單展開定義即可滿足：
```{.haskell .invisible}
mapFusionFuse1 :: (a -> b) -> (c -> a) -> c -> List a -> List b
mapFusionFuse1 f g x ys =
```
```haskell
      map f (g x : ys)
 ===    {- |map| 之定義 -}
      f (g x) : map f ys {-"~~."-}
```
:::

將上述例子與第\@ref{sec:induction-lists}節的歸納證明比較。
歸納證明中，最關鍵的是「使用歸納步驟」的一步，而使用摺融合定理的證明卻沒有這步 --- 歸納步驟的使用被包裝、隱藏在摺融合定理中了。
而上述例子中關於融合條件的證明，恰巧是原歸納證明中和問題本身最相關的部分。

我們可說：摺融合定理之於證明，就如同摺之於程式。
摺是抽象出的常見程式骨架，將拆解輸入串列、做遞迴呼叫等動作包裝起來。
有了摺，我們不需自己做遞迴呼叫，只需填入針對特定問題的 |f|, |e| 等參數的值。
摺融合定理則是抽象出的常見證明骨架，將狀況分析、使用歸納假設等動作包裝起來。
有了摺融合定理，我們不需自己做狀況分析、引用歸納假設，只需填入針對這個問題的融合條件的證明。

事實上，|map| 融合定理是下述定理的特例：
:::{.theorem title="|foldr|-|map| 融合定理" #thm:foldr-map-fusion}
  |foldr f e . map g = foldr (f . g) e|.
:::
我們時常看到 |foldr| 與 |map| 一起出現，此時定理\@ref{thm:foldr-map-fusion} 相當好用。
:::{.example #eg:foldr-sum-map}
我們嘗試證明 |sum . map (2*) = (2*) . sum|.
首先考慮等號左手邊的 |sum . map (2*)|. 由於 |sum| 是一個 |foldr|, 我們可用定理\@ref{thm:foldr-map-fusion}將該式合併為一個 |foldr|:
```{.haskell .invisible}
sumMapTwoTimesPf :: List Int -> Int
sumMapTwoTimesPf =
```
```haskell
       sum . map (2*)
  ===    {- |sum| 之摺定義 -}
       foldr (+) 0 . map (2*)
  ===    {- 定理\ref{thm:foldr-map-fusion}: |foldr|-|map| 融合 -}
       foldr ((+).(2*)) 0 {-"~~."-}
```
{.nobreak}另一方面，|(2*) . sum| 可以融合成同一個 |foldr|:
```spec
       (2*) . sum
  ===  (2*) . foldr (+) 0
  ===    {- 摺融合 -}
       foldr ((+).(2*)) 0 {-"~~."-}
```
{.nobreak}其中的融合條件證明如下：
```{.haskell .invisible}
sumMapTwoTimesFusion :: Int -> Int -> Int
sumMapTwoTimesFusion x y =
```
```haskell
      2*(x+y)
 ===   {- 乘法與加法之分配率 -}
      2*x + 2*y
 ===   {- |(.)| 之定義 -}
      ((+) . (2*)) x (2*y) {-"~~."-}
```
{.nobreak}由此我們證明了 |sum . map (2*) = (2*) . sum|.
:::

許多等式可用類似的模式證明：為證明 |e1 = e2|, 我們對兩邊都做融合，看是否能製造出同一個 |foldr|.
:::{.example #eg:foldr-map-append}
回顧練習\@ref{ex:map-append}：證明對所有 |f|, |xs|, 與 |ys|, |map f (xs ++ ys) = map f xs ++ map f ys|. 若把 |xs| 提出，這相當於證明：
```spec
  map f . (++ys) = (++ map f ys) . map f  {-"~~."-}
```
{.nobreak}其中 |(++ys)| 是 |foldr|. 因此我們可使用摺融合與 |foldr|-|map| 融合：
```{.haskell .invisible}
-- mapAppendFusion :: Int -> List Int -> Int
mapAppendFusion f ys =
```
```haskell
      (++ map f ys) . map f
 ===    {- |foldr|-|map| 融合 -}
      foldr ((:) . f) (map f ys)
 ===    {- 摺融合 -}
      map f . (++ ys) {-"~~."-}
```
{.nobreak}其中，最後一步的融合條件為
```spec
     map f (x : zs)
===    {- |map| 之定義 -}
     f x : map f zs
===    {- |(.)| 之定義 -}
     ((:) . f) x (map f zs) {-"~~."-}
```
{.nobreak}雖然看來複雜，其實是運用符號、展開定義即可證成的性質。
:::

在本節的許多例子中，使用摺融合定理大大簡化了證明 --- 幾乎到了只要把式子寫下就快要證完了，「沒什麼可說」的地步。我們再看最後一個例子。

:::{.example #eg:foldr-sunConcatMapSum}
考慮證明第\@ref{sec:data-prog-proof}節中提及的性質: |sum . concat = sum . map sum|.
我們可使用 |foldr|-|map| 融合定理與摺融合定理：
```{.haskell .invisible}
sumConcatMapSum :: List (List Int) -> Int
sumConcatMapSum =
```
```haskell
      sum . map sum
 ===  foldr (+) 0 . map sum
 ===    {- |foldr|-|map| 融合 -}
      foldr (\xs n -> sum xs + n) 0
 ===    {- 摺融合 -}
      sum . foldr (++) []
 ===  sum . concat {-"~~."-}
```
{.nobreak}第二步的 |foldr|-|map| 融合能成立的原因是 |(+) . sum| 展開之後確實成為 |(\xs n -> sum xs + n)|.
這一步也可改用摺融合定理證明，其融合條件為 |sum (sum xs : ys) = sum xs + sum ys|, 只需展開定義即可證成。

倒數第二步的摺融合的條件為：|sum (xs ++ ys) = sum xs + sum ys|.
這是第\@ref{sec:data-prog-proof}節的證明中必須發明的關鍵性質。
我們再一次看到：使用摺融合定理讓我們只需提供一個證明中最與問題相關的關鍵部分。
:::

:::{.exlist}
:::{.exer #ex:foldr-map-fusion}
請用摺融合證明 |foldr|-|map| 融合定理(\@ref{thm:foldr-map-fusion}).
:::
:::{.exer #ex:foldr-length-concat}
使用 |foldr|-|map| 融合和摺融合證明 |sum . map length = length . concat|.
:::
:::{.exans .compact}
```{.haskell .invisible}
lengthConcatMapLength :: List (List a) -> Int
lengthConcatMapLength =
```
```haskell
      sum . map length
 ===    {- |sum = foldr (+) 0|, |foldr|-|map| 融合 -}
      foldr ((+) . length) 0
 ===    {- 摺融合 -}
      length . foldr (++) []
 ===  length . concat {-"~~."-}
```
{.nobreak}其融合條件證明如下：
```{.haskell .invisible}
lengthConcatMapLengthFusion :: List a -> List a -> Int
lengthConcatMapLengthFusion xs ys =
```
```haskell
       length (xs ++ ys)
  ===    {- |length| 與 |(++)| 的同態性 -}
       length xs + length ys
  ===    {- |(.)| 之定義 -}
       ((+) . length) xs (length ys) {-"~~."-}
```
:::
:::{.exer #ex:mapConcat-concatMapMap}
使用摺融合定理證明對所有 |f|, |map f . concat = concat . map (map f)|.
:::
:::{.exer #ex:map-filter-split}
給定 |f, g :: a -> List a| 與 |p :: a -> Bool|, 試證明：
如果 |filter p (f x) = if p x then g x else []|, 則 |concat . map (filter p . f) = concat . map g . filter p|.
:::
:::{.exans}
回顧：|filter p = foldr (\x xs -> if p x then x:xs else xs) []|,
|concat = foldr (++) []|.
我們演算如下：
```{.haskell .invisible}
mapFilterSplit :: (a -> List a) -> (a -> List a) -> (a -> Bool) -> List a -> List a
mapFilterSplit f g p =
```
```haskell
      concat . map g . filter p
 ===    {- 摺融合，如下述 -}
      foldr (\x ys -> filter p (f x) ++ ys) []
 ===    {- |foldr|-|map| 融合，如下述 -}
      concat . map (filter p . f) {-"~~."-}
```
{.nobreak}摺融合的條件為：
```{.haskell .invisible}
mapFilterSplitFuse :: (a -> List a) -> (a -> List a) -> (a -> Bool) ->
                         a -> List a -> List a
mapFilterSplitFuse f g p x xs =
```
```haskell
      concat (map g (if p x then x:xs else xs))
 ===    {- |concat . map g| 分配進 |if| 之中 -}
      if p x then g x ++ concat (map g xs) else concat (map g xs)
 ===    {- 提出 |concat (map g xs)| -}
      (if p x then g x else []) ++ concat (map g xs)
 ===    {- 假設 -}
      filter p (f x) ++ concat (map g xs) {-"~~."-}
```
{.nobreak}至於 |foldr|-|map| 融合, 只需驗證 |((++) . filter p . f) x ys| 確實等於 |filter p (f x) ++ ys|.

:::
:::

### 以摺融合生成程式 {#sec:foldr-program-gen}

如前所述，另一種使用摺融合的理由是生成程式：我們希望 |h . foldr f e| 能在一個 |foldr| 之中完成。
此時我們已知 |h|, |f|, 與 |e|, 希望用融合條件找出適合的步驟函數。
:::{.example #ex:sum-map-square-fusion}
回顧第\@ref{sec:fold-unfold-transform}節的例子：
給定 |sumsq = sum . map square|，我們希望找出一個不產生中間串列的版本。
由於 |map square| 是一個 |foldr|, 我們嘗試將 |sum| 融合進 |map square| 中，
希望找出能滿足 |sumsq = foldr g e| 的 |g| 與 |e| .
顯然 |e = sumsq [] = 0|.
為了找出滿足融合條件的步驟函數 |g|, 我們推算：
```{.haskell .invisible}
sumsqFusionCond :: Int -> List Int -> Int
sumsqFusionCond x xs =
```
```haskell
      sum (square x : xs)
 ===    {- |sum| 之定義 -}
      square x + sum xs
 ===    {- 提出 |x| 與 |sum xs| -}
      (\x y -> square x + y) x (sum xs) {-"~~."-}
```
{.nobreak}因此，根據定理\@ref{thm:foldr-fusion}, |sumsq = foldr (\x y -> square x + y) 0|.
:::

:::{.example #ex:minimumMapSumInits}
給定一個整數串列，其中由左到右的數字表示對一個帳戶存款或提款的金額：正數為存款、負數為提款。
我們想確定在任何一個時刻帳戶金額不至於變成負數。
一個可能做法是：對該串列的每一個前段算總和，我們可得到每個時刻的帳戶金額。
接著看看其中最小值是否為負數即可。
定義函數 |noOverdraft| 如下：
```spec
noOverdraft :: Int -> Bool
noOverdraft = (>= 0) . minimum . map sum . inits {-"~~."-}
```
{.nobreak}我們試著導出一個比較快速的版本。

```texonly
%{
%format step1
%format step2
%format step3
```
為增進效率，我們試試看能否把 |minimum . map sum . inits| 合併為一個 |foldr|.
回顧：|inits = foldr (\x xss -> [] : map (x:) xss) []|.
我們可以一口氣把 |minimum . map sum| 融合進 |inits|, 也可分兩次進行，先將 |map sum . inits| 融合成一個 |foldr|, 再與 |minimum| 融合。

此處我們嘗試後者，先將 |map sum . inits| 融合。基底值為 |map sum [[]] = [0]|, 而步驟函數 |step1| 須滿足的融合條件為 |map sum ([] : map (x:) xss) = step1 x (map sum xss)|. 試計算如下：
```{.haskell .invisible}
mapSumInitsFuse :: Int -> List (List Int) -> List Int
mapSumInitsFuse x xss =
```
```haskell
      map sum ([] : map (x:) xss)
 ===  0 : map sum (map (x:) xss)
 ===   {- |map| 融合 -}
      0 : map (sum . (x:)) xss
 ===   {- |sum (x:xs) = x + sum xs|, |map| 融合 -}
      0 : map (x+) (map sum xss) {-"~~."-}
```
{.nobreak}因此我們得到
```{.haskell .invisible}
mapSumInits :: List Int -> List Int
mapSumInits =
```
```haskell
  map sum . inits === foldr (\x ys -> 0 : map (x+) ys) [0] {-"~~."-}
```

下一步是將 |minimum| 融合進 |map sum . inits|. 基底值為 |minimum [0] = 0|, 而步驟函數 |step2| 須滿足 |minimum (0 : map (x+) ys) = step2 x (minimum ys)|. 計算如下：
```{.haskell .invisible}
minimumSumInitsFuse :: Int -> List Int -> Int
minimumSumInitsFuse x ys =
```
```haskell
      minimum (0 : map (x+) ys)
 ===  0 `min` minimum (map (x+) ys)
 ===    {- |minimum (x+) ys = x + minimum ys|，後述 -}
      0 `min` (x + minimum ys) {-"~~."-}
```
{.nobreak}最後一步使用的性質 |minimum (x+) ys = x + minimum ys| 尚待證明，其關鍵性質是 |(x+)| 可分配進 |(`min`)| 之中：|x + (y `min` z) = (x + y) `min` (x + z)|. 總之，我們得到
```{.haskell .invisible}
geqMinimumSumInits :: List Int -> Bool
geqMinimumSumInits =
```
```haskell
      noOverdraft
 ===  (>= 0) . minimum . map sum . inits
 ===  (>= 0) . foldr (\x y -> 0 `min` (x + y)) 0 {-"~~."-}
```
{.nobreak}這是一個只需線性時間的演算法。

我們能否把 |(>=0)| 也融入 |foldr| 之中呢？要使這個融合成立，我們得找到滿足
|0 `min` (x+y) >= 0 <=> step3 x (y >= 0)| 的 |step3|. 演算如下：
```spec
     0 `min` (x+y) >= 0
<=>    {- |a `min` b >= c <=> a >= c && b >= c| -}
     0 >= 0 && x+y >= 0
<=>  x + y >= 0
<=>    {- 希望找到這樣的 |step3| -}
     step3 x (y>=0) {-"~~."-}
```
{.nobreak}然而我們無法找到這樣的 |step3| --- 僅由 |y>=0| 我們無法得知 |x+y >= 0| 是否成立。
我們可說 |(>=0)| 丟失了太多資訊，使得融合無法成立。

也由於同樣的理由，如果我們最初把問題定義為：
```spec
  noOverdraft = and . map (>=0) . map sum . inits {-"~~,"-}
```
{.nobreak}函數 |map (>= 0)| 將無法融合進 |map sum . inits| 之中。
```texonly
%} %format
```
:::

使用摺融合論證兩個式子相等的證明常有如下的形式：
```spec
     h1 . foldr f1 e1
===    {- 摺融合定理 -}
     foldr g (h1 e1)
===    {- 摺融合定理 -}
     h2 . foldr f2 e2 {-"~~."-}
```
{.nobreak}此時，我們也常需要藉由兩個融合條件之一來發現步驟函數 |g| 是什麼。

:::{.example #eg:foldr-length-sublists}
習題 \@ref{ex:length-sublists} 曾證明 |length . sublists = exp 2 . length|.
此處我們用摺融合定理試試看。

考慮等式的左手邊，我們嘗試將 |length . sublists| 融合為一個 |foldr|.
由於 |sublists = foldr (\x xss -> xss ++ map (x:) xss) [[]]|（習題 \@ref{ex:perms-sublists-splits-foldr}(2)），融合後的 |foldr| 之基底值為 |length [[]] = 1|.
為找出步驟函數，我們推算：
```{.haskell .invisible}
lengthSublistFuse :: a -> List (List a) -> Int
lengthSublistFuse x xss =
```
```haskell
      length (xss ++ map (x:) xss)
 ===  length xss + length (map (x:) xss)
 ===    {- |length (map f) = length| -}
      2 * length xss {-"~~,"-}
```
{.nobreak}由此得到步驟函數 |(\x n -> 2 * n)|.

因此該等式可證明如下：
```spec
     length . sublists
===  length . foldr (\x xss -> xss ++ map (x:) xss) [[]]
===    {- 摺融合定理，如上 -}
     foldr (\x n -> 2 * n) 1
===    {- 摺融合定理，如下 -}
     exp 2 . foldr Suc Zero
===  exp 2 . length {-"~~."-}
```
{.nobreak}在第二次摺融合中，基底值 |exp 2 Zero| 確實是 |1|.
融合條件為 |exp 2 (Suc n) = 2 * exp 2 n|.
:::

:::{.exlist}
:::{.exer #ex:foldr-map-sum-inits}
回顧例\@ref{ex:minimumMapSumInits}. 試著將 |map (>=0)| 融入 |map sum . inits| 中，說說看為何該融合會失敗。
:::
:::{.exans .compact}
我們需要滿足融合條件 |map (>=0) (0 : map (x+) ys) = step x (map >=0 ys)| 的 |step|.
演算如下：
```spec
     map (>=0) (0 : map (x+) ys)
===  True : map ((>=0) . (x+)) ys
===  step x (map (>=0) ys) {-"~~."-}
```
{.nobreak}然而我們無法由 |map (>=0) ys| 算出 |map ((>=0) . (x+)) ys|.
:::
:::{.exer #ex:foldr-sum-distributivity}
使用摺融合定理證明 |sum (xs ++ ys) = sum xs + sum ys|.
**提示**：這相當於證明 |sum . (++ys) = (+ (sum ys)) . sum|.
:::
:::{.exans .compact}
```{.haskell .invisible}
sumAppendPlus ys =
```
```haskell
      sum . (++ys)
 ===  sum . foldr (:) ys
 ===    {- 摺融合 -}
      foldr (+) (sum ys)
 ===    {- 摺融合 -}
      (+ (sum ys)) . foldr (+) 0
 ===  (+ (sum ys)) . sum {-"~~."-}
```
{.nobreak}其中第一個摺融合的條件為 |sum (x:xs) = x + sum xs| ---
我們由此發現融合後的步驟函數為 |(+)|.
第二個摺融合的條件證明如下：
```{.haskell .invisible}
sumAppendPlusFusionCond x y ys =
```
```haskell
      (+ (sum ys)) (x + y)
 ===  (x + y) + sum ys
 ===  x + (y + sum ys)
 ===  x + ((+ (sum ys)) y) {-"~~."-}
```
:::
:::{.exer #ex:foldr-lengthFan-SucLength}
參考習題 \@ref{ex:fan-foldr}, 使用摺融合定理證明 |length (fan y xs) = Suc (length xs)|.
:::
:::{.exans}
相當於證明 |length . fan y = Suc . length|. 推論如下：
```spec
     length . fan y
===  length . foldr (\x xss -> (y:x: tail (head xss)) : map (x:) xss) [[y]] {-"~~."-}
===    {- 摺融合定理 -}
     foldr Suc 1
===    {- 摺融合定理 -}
     Suc . foldr Suc Zero
===  Suc . length {-"~~."-}
```
{.nobreak}其中第一次融合的融合條件可證明如下：
```spec
     length ((y:x: tail (head xss)) : map (x:) xss)
===    {- |length| 之定義 -}
     Suc (length (map (x:) xss))
===    {- |length . map f = length| -}
     Suc (length xss) {-"~~."-}
```
{.nobreak}由此發現步驟函數為 |Suc|.
第二次融合的融合條件則只需展開定義即可證成。
:::
:::{.exer #ex:foldr-decimal}
回顧第\@ref{sec:exp-binary-roll}節中將反轉表示的二進位數字轉為自然數的函數 |decimal :: List Bool -> Nat|.
該函數可寫成一個摺：
```spec
decimal = foldr (\c n -> if c then 1 + 2 * n else 2 * n) 0 {-"~~"-}
```
{.nobreak}請使用摺融合將 |exp b . decimal| 表示成單一的摺。
:::
:::{.exans}
基底值為 |base = exp b 0 = 1|.
為找出步驟函數，我們推論：
```spec
     exp b (if c then 1 + 2 * n else 2 * n)
===    {- 函數分配進 |if| -}
     if c then exp b (1 + 2 * n) else exp b (2 * n)
===    {- 因 $m^{x+y} = m^x \times m^y$ -}
     if c then b * exp b (2 * n) else exp b (2 * n)
===    {- 因 $m^{2n} = (m^n)^2$, 回顧：|square x = x * x| -}
     if c then b * square (exp b n) else square (exp b n) {-"~~."-}
```
{.nobreak}因此可得
```spec
  exp b . decimal = foldr (\d x -> if c  then b * square x
                                         else square x) 1 {-"~~."-}
```
:::
:::

{title="摺融合與尋找歸納定義"}
回顧：|id :: List a -> List a| 可以寫成一個 |foldr| --- |id = foldr (:) []|.
而任何函數 |f :: List a -> b| 都等於 |f . id|.
如果我們將 |f| 與 |id| 融合，會發生什麼事呢？
首先我們需要找出基底值 |f []| 是什麼。
接著我們要找到滿足 |f (x:xs) = step x (f xs)| 的步驟函數 |step|.
但這其實就是使用展開-收回轉換尋找 |f| 的歸納定義！
只是此處要求的歸納定義比較嚴格：在 |f xs| 之外不能使用 |xs|.

確實，第\@ref{sec:fold-unfold-transform}與\@ref{sec:fold-unfold-transform-efficiency}節中許多尋找歸納定義的演算都可以視為使用摺融合生成程式的例子。
以第\@ref{sec:poly-horner}節的 |poly| 為例。
找出其歸納定義的過程可以視為摺融合：
```spec
   poly x
=  poly x . id
=   {- |id = foldr (:) []| -}
   poly x . foldr (:) []
=   {- 摺融合定理 -}
   foldr step (poly x []) {-"~~."-}
```
{.nobreak}其中基底值 |poly x [] = 0|.
而函數 |step| 須滿足融合條件 |poly x (a:as) = step a (poly x as)|。
尋找 |step| 的過程和第\@pageref{ex:polyDer1}頁的計算完全相同。
我們會得到
```spec
  poly x (a : as) = a + (poly x as) * x {-"~~."-}
```
{.nobreak}到此為止我們便找到了 |poly x| 的歸納定義。
也可以說，我們已得知 |poly x = foldr (\a b -> a + b * x) 0|.

### 掃描 {#sec:scan-lemma}

本節將介紹一個本書首次提及，初見時較難理解，但在許多演算法中扮演重要角色的組件函數：*掃描*（*scan*）。\index{scan 掃描}

如我們所知，函數 |sum :: List Int -> Int| 計算一個串列的總和。
如果我們想計算一個串列由右到左的*累計和*，例如當給定串列 |[3,7,2,4]|，我們希望得到 |[16,13,6,4,0]|（其中 |6 = 2 + 4|, |13 = 7 + 2 + 4|，|16 = 3 + 7 + 2 + 4|, 而 |0| 是空串列的和），該怎麼做呢？

在第\@ref{sec:list-segments}節中，我們曾提及計算一個串列所有*後段*(*suffixes*)的函數 |tails :: List a -> List (List a)|。\index{list 串列!suffix 後段}
例如，|tails [3,7,2,4]| 將得到 |[[3,7,2,4],| |[7,2,4],| |[2,4],| |[4],| |[]]|。對串列的每一個後段算總和，我們便得到累計和 |[16,13,6,4,0]| 了：
```haskell
runsum :: List Int -> List Int
runsum = map sum . tails {-"~~."-}
```
{.nobreak}由於使用多個 |sum| 函數走訪每個後段，如此定義出的 |runsum| 將是一個執行時間為 $O(n^2)$ 的函數。
但讀者想必已覺得可不用如此費事：我們應該可以在由右到左走訪串列的過程中*記住目前為止的和*，避免重算 |sum|。這該怎麼做呢？

回想： |sum| 可寫成一個摺。因此我們可稍微推廣一下，定義函數 |scanr| 如下：
```spec
scanr :: (a -> b -> b) -> b -> List a -> List b
scanr f e = map (foldr f e) . tails {-"~~."-}
```
{.nobreak}給定一個串列 |xs|, |scanr f e| 先算出 |xs| 的所有後段，
然後對每一個後段都做 |foldr f e|. \index{list 串列!suffix 後段}
前述的 |runsum| 其實是 |scanr| 的特例：
|runsum = scanr (+) 0|.

如果把上述的 |scanr| 定義當作演算法，處理長度為 |n| 的串列時呼叫 |f| 的次數為 $O(n^2)$.
我們找找看是否有比較快的演算法。

第 \@ref{sec:more-folds-on-lists} 節中提及 |tails| 是一個 |foldr|:
```spec
tails = foldr (\x xss -> (x : head xss) : xss) [[]] {-"~~,"-}
```
{.nobreak}也許我們可試著把 |map (foldr f e)| 融合入 |tails| 中，看看是否能找出一個較有效率的 |scanr| 定義。
其融合條件如下：
```{.haskell .invisible}
scanrFusionCond :: (a -> b -> b) -> b -> a -> List (List a) -> List b
scanrFusionCond f e x xss =
```
```haskell
      map (foldr f e) ((x : head xss) : xss)
 ===    {- |map| 之定義 -}
      foldr f e (x : head xss) : map (foldr f e) xss
 ===    {- |foldr| 之定義 -}
      f x (foldr f e (head xss)) : map (foldr f e) xss
 ===    {- |g (head ys) = head (map g ys)|; 令 |g := foldr f e|, |ys := xss| -}
      f x (head (map (foldr f e) xss)) : map (foldr f e) xss
 ===    {- 取出 |map (foldr f e) xss| -}
      let ys = map (foldr f e) xss
      in f x (head ys) : ys {-"~~."-}
```
{.nobreak}於是我們推導出了 |scanr| 的另一個定義：
:::{.lemma title="掃描引理" #lma:scan-lemma}
對所有 |f|, |e|,
```spec
scanr f e = foldr (\x ys -> f x (head ys) : ys) [e] {-"~~."-}
```
:::

若將 |foldr| 的定義展開，函數 |scanr| 可寫成下列的歸納形式，也許比較容易理解：
```spec
scanr f e []      = [e]
scanr f e (x:xs)  = f x (head ys) : ys {-"~~,"-}
    where ys = scanr f e xs {-"~~."-}
```
{.nobreak} 在第 \@ref{sec:more-folds-on-lists} 節中，使得 |tails| 能寫成一個 |foldr| 的重要性質是|head (tails xs) = xs| -- |tails xs| 的第一個元素就是 |xs| 本身。使用 |tails| 定義的 |scanr| 自然繼承了相關的性質：|scanr f e xs| 的第一個元素就是 |foldr f e xs|, 因此可直接用 |head| 取出，不需每次重新計算。
用本節開頭的例子說明，以下我們令 |scr = (\x ys -> x + head ys : ys)|:
```spec
     scanr (+) 0 [3,7,2,4]
===  scr 3 (scr 7 (scr 2 (scr 4 [0])))
===  scr 3 (scr 7 (scr 2 [4 + 0, 0]))
===  scr 3 (scr 7 [2 + 4 + 0, 4 + 0, 0])
===  scr 3 [7 + 2 + 4 + 0, 2 + 4 + 0, 4 + 0, 0]
===  [3 + 7 + 2 + 4 + 0, 7 + 2 + 4 + 0, 2 + 4 + 0, 4 + 0, 0]
===  [16,13,6,4,0] {-"~~,"-}
```
{.nobreak}其中每個 |scr| 都可直接使用之前累積計算的結果，不用從頭加起。

### 香蕉船定理 {#sec:banana-split}

第\@ref{sec:tupling-conclude}節簡短地提到一個例子：
令 |sumlen = fork sum length|,
^[分裂運算元 |fork| 的定義請參照第\@ref{sec:pairs}節，\@pageref{par:split-product}頁。]
直接執行的話，|sum| 與 |length| 將各自走訪輸入串列一次，
但我們可推導出 |sumlen| 的歸納定義，得到一個只走訪串列一次的版本。

上述例子還可以更通用一些。考慮 |fork (foldr f1 e1) (foldr f2 e2)| --- 這個算式拿一個串列當輸入，兩個 |foldr| 分別將串列走訪一次，兩個結果分別存放在序對中。我們有可能將它變成一個摺（因此只走訪串列一次）嗎？
下述的「香蕉船定理(banana-split theorem)」告訴我們：*含兩個摺的分裂，可以寫成一個摺*。
\index{banana-split 香蕉船定理}
:::{.theorem title="香蕉船定理" #thm:banana-split}
給定 |f1 :: a -> b -> b|, |e1 :: b| , |f2 :: a -> c -> c|, |e2 :: c|, 下述等式成立：
```{.haskell .invisible}
bananaSplit :: (a -> b -> b) -> b -> (a -> c -> c) -> c -> List a -> (b :* c)
bananaSplit f1 e1 f2 e2 =
```
```haskell
 fork (foldr f1 e1) (foldr f2 e2) === foldr g (e1,e2) {-"~~,"-}
```
```{.haskell .invisible}
 where g x (y,z) = (f1 x y, f2 x z)
```
{.nobreak}其中 |g x (y,z) = (f1 x y, f2 x z)|.
:::
分裂運算元 |fork| 的英文稱呼是 ``split'', 在程式推導圈內有時會用一套稱作「香蕉括號(banana brackets)」的符號表示摺，兩者合起來便是 ``banana-split'' --- 甜點「香蕉船」的英文名稱。

定理\@ref{thm:banana-split}相當於把兩個處理同一份資料的迴圈合併成一個。
但如同第\@ref{sec:tupling-conclude}節提及，這並不保證效率會比較好。
我們會使用定理\@ref{thm:banana-split}的原因可能是如果確定某函數是摺，
我們能做更多後續處理（例如，使用掃描定理或其他只對摺成立的性質）。

:::{.exlist}
:::{.exer #ex:banana-split}
證明香蕉船定理。
你可以在輸入串列上做歸納證明，
也可以利用
|fork (foldr f1 e1) (foldr f2 e2) = fork (foldr f1 e1) (foldr f2 e2) . id
 = fork (foldr f1 e1) (foldr f2 e2) . foldr (:) []| 的特性，使用摺融合定理。
:::
:::

「組對」常可視為分裂與 |id| 的融合。
例如，在第\@ref{sec:steep}節的陡串列問題中，我們定義
|steepsum xs = (steep xs, sum xs)|，並試著推導其歸納定義。
該過程也可視為將 |fork steep sum| 與 |id| 融合：
```{.haskell .invisible}
steepSumId :: List Int -> (Bool :* Int)
steepSumId =
```
```haskell
     fork steep sum
 ===   {- |f . id = f| -}
     fork steep sum . id
 ===   {- |id = foldr (:) id| -}
     fork steep sum . foldr (:) []
 ===   {- 摺融合 -}
     foldr (\x (b, s) -> (x > s && b, x + s)) (True, 0) {-"~~."-}
```
{.nobreak}其融合條件的證明與第\@ref{sec:steep}節中幾乎相同。

### 累積參數與摺融合 {#sec:accum-param-fold-fusion}

第\@ref{sec:accumulating-param}節介紹的「累積參數」技巧也常可視為高階函數與摺的融合。
以第\@ref{sec:reversal-append}節的經典例子 --- 串列反轉為例。
函數 |reverse :: List a -> List a| 是一個 |foldr|:
```spec
reverse = foldr (\x xs -> xs ++ [x]) [] {-"~~."-}
```
{.nobreak}為增進其效率，我們創造了函數 |revcat|，其定義為：
```spec
revcat :: List a -> List a -> List a
revcat xs ys = reverse xs ++ ys {-"~~."-}
```
{.nobreak}但如果把參數都移除，上述定義其實等同於：
```spec
revcat = (++) . reverse {-"~~."-}
```
{.nobreak}推導 |revcat| 的歸納定義就是計算 |(++)| 與 |reverse| 的融合！

為了導出一個較快的 |revcat| 實作，我們嘗試把 |(++) . reverse| 融合為一個 |foldr|.
其推導大綱如下：
```{.haskell .invisible}
appendReverseDer00 :: List a -> List a -> List a
appendReverseDer00 =
```
```haskell
      (++) . reverse
 ===  (++) . foldr (\x xs -> xs ++ [x]) []
 ===    {- 摺融合，試著計算出 |base| 與 |step| -}
      foldr step base {-"~~."-}
```
```{.haskell .invisible}
 where step :: a -> (List a -> List a) -> List a -> List a
       step = undefined
       base :: List a -> List a
       base = undefined
```
{.nobreak}我們可暫停一下，看看這個式子的型別。
函數 |(++)| 的型別為 |List a -> (List a -> List a)|, |(++) . reverse| 與 |foldr step base| 的型別也相同。
如果摺融合成功，我們會得到的是一個*傳回函數的 |foldr|* --- 輸入為 |List a|, 輸出為 |List a -> List a|.
其中 |base| 的型別為 |List a -> List a|, 而 |step| 的型別將是 |a -> (List a -> List a) -> (List a -> List a)| --- |step x| 將一個函數轉成另一個函數。

根據摺融合定理，基底值 |base| 是
```spec
  (++) []  = (\xs -> (++) [] xs)
           = (\xs -> [] ++ xs)
           = (\xs -> xs)
           = id {-"~~."-}
```
{.nobreak}步驟函數 |step| 須滿足的融合條件如下
```{.haskell .invisible}
appendReverseFuse00 :: a -> List a -> List a -> List a
appendReverseFuse00 x xs =
```
```haskell
     (++) ((\x xs -> xs ++ [x]) x xs) === step x ((++) xs) {-"~~."-}
```
```{.haskell .invisible}
 where step :: a -> (List a -> List a) -> List a -> List a
       step = undefined
```
{.nobreak}簡單地化簡等號左手邊，我們得到：
```spec
     (++) (xs ++ [x]) === step x ((++) xs) {-"~~."-}
```
{.nobreak}這個式子無法再規約，因為 |(++)| 還需要一個參數。
因此我們根據外延相等（定義\@ref{def:extensional-eq}），在等號兩邊各補一個參數 |ys|:
```spec
     (++) (xs ++ [x]) ys === step x ((++) xs) ys{-"~~."-}
```
{.nobreak}為找出 |step|, 演算如下：
```{.haskell .invisible}
appendReverseFuse01 :: a -> List a -> List a -> List a
appendReverseFuse01 x xs ys =
```
```haskell
      (++) (xs ++ [x]) ys
 ===  (xs ++ [x]) ++ ys
 ===    {- |(++)| 之結合律 -}
      xs ++ ([x] ++ ys)
 ===   {- |(.)| 之定義 -}
     (((++) xs) . (x:)) ys
 ===   {- 將 |x|, |((++) xs)|, 與 |ys| 提出 -}
     (\x f -> f . (x:)) x ((++) xs) ys {-"~~."-}
```
{.nobreak}根據外延相等，我們已證明
```spec
  (++) (xs ++ [x]) = (\x f -> f . (x:)) x ((++) xs) {-"~~."-}
```
{.nobreak}因此 |step = (\x f -> f . (x:))|, 而 |revcat| 可寫成如下的摺：
```haskell
revcat = foldr (\x f -> f . (x:)) id {-"~~."-}
```
{.nobreak}例如 |revcat "abc" = id . ('c':) . ('b':) . ('a':)|,
而 |revcat "abc" ys = 'c' : ('b' : ('a' : ys))|.

### 引入脈絡 {#sec:bring-in-context}
\index{fold 摺!bringing in the context 引入脈絡}

第\@ref{sec:foldr-fusion}節開頭（第\@pageref{para:bring-in-context-prelim}頁）曾提及：
使用摺融合定理將 |h . foldr f e| 融合成 |foldr g (h e)| 時，融合條件 |h (f x y) = g x (h y)| 並不需對所有 |y| 都成立，而只需對在 |foldr f e| 的值域內的 |y| 成立即可。
截至目前為止我們看了不少摺融合的例子，但我們所證明的融合條件，均是較寬鬆、對所有 |y| 都成立的。
我們還沒看過只對特定 |y| 成立（因此可能較難證明的）融合條件。

知道「|y| 在 |foldr f e| 的值域內」，意味著證明融合條件時，我們可以假設 |y| 滿足所有 |foldr f e| 的傳回值該滿足的性質。習慣上，「使用這些性質」被稱作「*引入脈絡*」(*bringing in the context*) --- 意指做證明時知道 |y| 不是任意的值，而是由 |foldr f e| 產生（有特定脈絡）的。此處我們看一個引入脈絡的簡單例子。

:::{.example #ex:suc-map-square}
回顧 |sumsq = sum . map square|.
我們在例\@ref{ex:sum-map-square-fusion}中曾導出 |sumsq = foldr (\x y -> square x + y) 0|.
現在考慮下述函數：
```spec
psuc n = if n >= 0 then n+1 else 0 {-"~~."-}
```
{.nobreak}如果參數是非負整數，|psuc| 將它加一，否則傳回 |0|.
我們能將 |psuc . sumsq| 融合為一個 |foldr| 嗎？

直覺看來，由於 |sumsq| 一定傳回非負整數，|psuc| 只是將其結果加一。
但如果使用摺融合，需要的融合條件是 |psuc (square x + y) = step x (psuc y)|.
我們找不到一個對任意 |x| 與 |y| 都能使該條件成立的 |step|.

此時我們需要引入脈絡：由於 |y| 是 |sumsq| 的結果，必定是個非負整數。
我們可證明對於非負整數 |m| 與 |n|,
```spec
     psuc (m + n) = m + psuc n {-"~~."-}
```
{.nobreak}由於 |square x| 與 |y| 都是非負整數，我們有
```spec
     psuc (square x + y) = square x + psuc y {-"~~."-}
```
{.nobreak}因此我們可選 |step x y = square x + y| --- 與 |sumsq| 的步驟函數相同。
至於基底值則是 |psuc 0 = 1|.
因此，
```spec
  psuc . sumsq = foldr (\x y -> square x + y) 1 {-"~~."-}
```
:::

例\@ref{ex:suc-map-square}是個刻意設計的、簡單的例子。在第TODO節中，我們會看到其他需要引入脈絡的演算法。

## 左摺、串列同構、與 Paramorphism {#sec:foldl-listHomo-para}

為了完整性，本節介紹與串列的摺相關的另外幾個組件函數。
初次閱讀時可跳過本節。

### 左摺 {#sec:foldl}

除了 |foldr|, Haskell 的標準函式庫有另一個函數 |foldl|, 名字中的字母 |l| 為「左」之意：
|foldr| 將串列中的元素往右括，|foldl| 則往左括，例如，
```spec
 foldl rhd e [x0,x1,x2,x3] = (((e `rhd` x0) `rhd` x1) `rhd` x2) `rhd` x3 {-"~~."-}
```
{.nobreak}有了 |foldl|, 串列反轉可直接定義為 |reverse = foldl (\xs x -> x:xs) []|.

函數 |foldl| 可在輸入串列的長度上歸納定義如下：
```spec
foldl :: (b -> a -> b) -> b -> List a -> b
foldl rhd e []         = e
foldl rhd e (xs++[z])  = foldl rhd e xs `rhd` z{-"~~."-}
```
{.nobreak}由於運算元 |rhd| 右邊的參數才是目前的元素，其型別為 |b -> a -> b|.
由此出發，我們不難導出下述將串列從左邊開始拆解的定義：
```spec
foldl rhd e []      = e
foldl rhd e (x:xs)  = foldl rhd (e `rhd` x) xs {-"~~."-}
```
{.nobreak}我們可注意到這是一個尾遞迴定義，\index{tail recursion 尾遞迴}
因此，如果將 |sum|, |prod| 等函數定義為 |foldl (+) 0|, |foldl (*) 1| 等等，執行時可不佔用堆疊的空間。
由於這個特性，對一些將 Haskell 用於著重效率的應用的人們來說，|foldl| 才是他們較常使用的「摺」。
^[為了效率因素更常被使用的可能是另一個嚴格(strict)版的函數 |foldl'|, 該函數在遞迴呼叫前會先將 |e `rhd` x| 規約成正規式，避免尚待計算的算式被累積著。]

關於 |foldl| 與 |foldr| 的關係，@Bird:98:Introduction 提及了三個定理。首先，
:::{.theorem title="第一對偶定理(The First Duality Theorem)" #thm:first-duality}
如果 |oplus :: a -> a -> a| 滿足遞移律，以 |e :: a| 為單位元素，則 |foldr oplus e xs = foldl oplus e xs|.
:::
提醒一下：該定理及本節的其他定理中，|xs| 需為歸納定義、有限長度的串列。
遞移律意指 |x `oplus` (y `oplus` z) = (x `oplus` y) `oplus` z| --- 由於此項要求，|oplus| 的型別得是 |a -> a -> a|. 由於 |(+)|, |(*)|, |(`min`)|, |(`max`)| 等運算元都有遞移律，|sum|, |prod|, |maixmum|, |minimum| 等函數都可用 |foldl| 定義。事實上，他們在標準 Haskell Report 中的定義便是如此。

定理\@ref{thm:first-duality}其實是下述定理的特例。
函數 |foldl| 有個尾遞迴定義，其中參數 |e| 的角色就像是個累積參數。
第\@ref{sec:tail-recursion}節中曾提及，尾遞迴函數時常和遞移律有關。
函數 |foldl| 是否也牽涉了某種遞移律呢？
:::{.theorem title="第二對偶定理(The Second Duality Theorem)" #thm:second-duality}
如果二元運算元 |lhd :: a -> b -> b| 及 |rhd :: b -> a -> b| 滿足 |x `lhd` (y `rhd` z) = (x `lhd` y) `rhd` z| 以及 |x `lhd` e = e `rhd` x|，
則 |foldr lhd e xs = foldl rhd e xs|.
:::

定理 \@ref{thm:second-duality} 中的 |x `lhd` (y `rhd` z) = (x `lhd` y) `rhd` z| 可視為一種擴充到兩個運算元的遞移律。定理 \@ref{thm:first-duality} 則是 |lhd = rhd| 的特殊情況。

定理 \@ref{thm:second-duality} 的證明頗值得研究：
:::{.proof}
我們在 |xs| 上做歸納。基底狀況 |xs := []| 中，等號兩邊都歸約為 |e|.
至於 |xs := x : xs| 的情況，我們把兩邊都化簡並使用歸納假設，推論如下：
```{.haskell .invisible}
sndDualityInd1 :: (a -> b -> b) -> (b -> a -> b) -> b -> a -> List a -> b
sndDualityInd1 lhd rhd e x xs =
```
```haskell
      foldr lhd e (x:xs)
 ===    {- |foldr| 之定義 -}
      x `lhd` foldr lhd e xs
 ===    {- 歸納假設 -}
      x `lhd` foldl rhd e xs
 ===    {- 論證如後述 -}
      foldl rhd (x `lhd` e) xs
 ===    {- 假設： |x `lhd` e = e `rhd` x| -}
      foldl rhd (e `rhd` x) xs
 ===    {- |foldl| 之定義 -}
      foldl rhd e (x:xs) {-"~~."-}
```
{.nobreak}在等式推論中段，我們希望 |x `lhd` foldl rhd e xs = foldl rhd (e `rhd` x) xs|.
這會需要另一個歸納證明。
但我們若直接證明此等式，到中途便會無法進行，且會發現我們需要稍做一下推廣，改證明一個較強的性質：
```{.equation #eq:sndDualityGen}
  |x `lhd` foldl rhd y xs = foldl rhd (x `lhd` y) xs {-"~~."-}|
```
兩者的差別是後者不針對特定的值 |e|, 而是任何的 |y|.
這是一個「較強的性質反而比較好證明」的例子。

等式\@eqref{eq:sndDualityGen}的證明如此進行：在 |xs := []| 的情況中，等號兩側都規約為 |x `lhd` y|.
歸納情況 |xs := z : xs| 證明如下：
```{.haskell .invisible}
sndDualityGen :: (a -> b -> b) -> (b -> a -> b) -> a -> b -> a -> List a -> b
sndDualityGen lhd rhd x y z xs =
```
```haskell
      x `lhd` foldl rhd y (z:xs)
 ===    {- |foldl| 之定義 -}
      x `lhd` foldl rhd (y `rhd` z) xs
 ===    {- 歸納假設 -}
      foldl rhd (x `lhd` (y `rhd` z)) xs
 ===    {- 假設：|x `lhd` (y `rhd` z) = (x `lhd` y) `rhd` z| -}
      foldl rhd ((x `lhd` y) `rhd` z) xs
 ===    {- |foldl| 之定義 -}
      foldl rhd (x `lhd` y) (z:xs) {-"~~."-}
```
:::

最後一個對偶定理則確認了我們的一個直覺理解：將一個串列反轉做 |foldl|, 便相當於 |foldr|:
:::{.theorem title="第三對偶定理(The Third Duality Theorem)" #thm:third-duality}
對所有 |f :: a -> b -> b|, |e :: b|, 以及 |xs :: List a|,
|foldr f e xs = foldl (flip f) e (reverse xs)|.
其中 |flip f x y = f y x|.
:::

### 串列同構 {#sec:list-homomorphism}

考慮函數 |h :: List a -> b|. 如果存在 |e :: b|, |f :: a -> b|, 和 |odot :: b -> b -> b| 使得 |h| 滿足下列等式：
```spec
h []          = e
h [x]         = f x
h (xs ++ ys)  = h xs `odot` h ys {-"~~,"-}
```
```{.haskell .invisible}
hom :: (b -> b -> b) -> (a -> b) -> b -> List a -> b
hom odot f e []  = e
hom odot f e [x] = f x
hom odot f e xs  = hom odot f e ys `odot` hom odot f e zs
    where n = length xs `div` 2
          (ys,zs) = (take n xs, drop n xs)
```
{.nobreak}我們便說 |h| 是一個*串列同構*(*list homomorphism*), 記為 |h = hom odot f e|.
\index{list homomorphism 串列同構}
注意第三個等式蘊含 |odot|（至少在 |h| 的值域內）須滿足結合律：
|h xs `odot` (h ys `odot` h zs) = h (xs++(ys++zs)) = h ((xs++ys)++zs) = (h xs `odot` h ys) `odot` h zs|.

串列同構有平行計算的可能性：計算 |hom odot f e xs| 時，如果 |xs| 有不只一個元素，我們可將 |xs| 由中間任意截成兩段，分別給不同的處理器計算，再將結果用 |odot| 結合。

顯然，|hom dot f e| 可以寫成 |foldr|, 也能寫成 |foldl|:
```{.haskell .invisible}
homFoldlFoldr :: (b -> b -> b) -> (a -> b) -> b -> List a -> b
homFoldlFoldr odot f e =
```
```haskell
  hom odot f e  === foldr (\x y -> f x `odot` y) e
                === foldl (\y x -> y `odot` f x) e {-"~~."-}
```
{.nobreak}下述定理則告訴我們反過來也成立：如果 |h| 同時可寫成 |foldr| 及 |foldl|, 則 |h| 是一個串列同構：
:::{.theorem title="第三同構定理(The Third Homomorphism Theorem)" #thm:third-homo-thm}
考慮 |h :: List a -> b|。如果存在 |e :: b|, |lhd :: a -> b -> b|, 及 |rhd :: b -> a -> b| 使得 |h = foldr lhd e = foldl rhd e|,
則存在 |odot :: b -> b -> b| 使得 |h = hom odot f e| （其中 |f x = x `lhd` e = e `rhd` x|）.
:::

### Paramorphism 與本原遞迴 {#sec:paramorphism}

如果我們把 |foldr| 的限制放寬，允許 |xs| 出現在遞迴呼叫之外，得到的模式稱為 *paramorphism*.
串列版的 paramorphism 可定義如下：
```haskell
para :: (a -> List a -> b -> b) -> b -> List a -> b
para f e []      = e
para f e (x:xs)  = f x xs (para f e xs) {-"~~."-}
```

```spec
para f e = fst . foldr (\x (y, xs) -> (f x xs y, x:xs)) (e, []) {-"~~."-}
```

## 自然數的摺 {#sec:foldN}

自然數可以視為有兩個建構元 |Zero| 和 |Suc| 的歸納資料結構。
我們也可為自然數定義一個摺：
```haskell
foldN :: (a -> a) -> a -> Nat -> a
foldN f e Zero     = e
foldN f e (Suc n)  = f (foldN f e n) {-"~~."-}
```
{.nobreak}和串列的情況類似，函數 |foldN f e| 拿一個自然數，將其中的 |Zero| 代換成 |e|, |Suc| 代換成 |f|.
留意型別：|Zero| 與 |Suc| 的型別分別是 |Nat| 與 |Nat -> Nat|,
|foldN| 要將一個型別為 |Nat| 的值轉變為型別為 |a| 的值,
因此 |e| 的型別為 |a|, 而 |f| 的型別為 |a -> a|.
為方便稱呼，我們也將 |e| 與 |f| 分別稱為基底值與步驟函數。

許多我們定義過的、自然數上的函數都可寫成自然數的摺：

  * |exp b = foldN (b*) 1|,
  * |(+n) = foldN (Suc) n|,
  * |(*n) = foldN (n+) 0|.

{.nobreak}自然數上的 |id :: Nat -> Nat| 也可寫成摺：|id = foldN (Suc) 0|.

自然數的摺也有一個融合定理：
:::{.theorem title="摺融合定理(自然數版)" #thm:foldN-fusion}
\index{fold 摺!fold fusion 摺融合}
給定 |f :: a -> a|, |e :: a|, |h :: a -> b|.
如果對所有在 |foldN f e| 值域中的 |x :: a|, 融合條件
|h (f x) = g (h x)| 成立, 則
```spec
h . foldN f e = foldN g (h e) {-"~~."-}
```
:::

:::{.example #eg:foldN-even}
判斷一個自然數是否為偶數的述語 |even :: Nat -> Bool| 可寫成一個摺:
```spec
  even = foldN not True {-"~~."-}
```
{.nobreak}函數 |even . (+n)| 判斷一個數值加上 |n| 之後是否為偶數。
由於 |(+ n) = foldN (Suc) n|, 我們可以嘗試把 |even| 融入 |(+n)|, 變成一個摺。
根據定理\@ref{thm:foldN-fusion}, 基底值為 |even n|;
而由於 |even (Suc n) = not (even n)|, 步驟函數為 |not|.
因此：
```spec
even . (+n) = foldN not (even n) {-"~~."-}
```
:::

:::{.exlist}
:::{.exer #ex:foldN-fib}
回顧第\@ref{sec:complete-induction}節中提到的費氏數定義：
```spec
fib 0      = 0
fib 1      = 1
fib (2+n)  = fib (1+n) + fib n {-"~~."-}
```
{.nobreak}若直接將上述定義當作演算法，我們得做許多重複的計算。
定義 |fib2 n = (fib (1+n), fib n)|.
請將 |fib2| 融合進 |id :: Nat -> Nat|, 以便得到一個遞迴呼叫次數為 $O(n)$ 的演算法。
:::
:::{.exans}
回顧 |id = foldN (Suc) 0|.
欲將 |fib2| 融入 |id|, 基底值為 |fib2 0 = (fib 1, fib 0) = (1,0)|.
為得到步驟函數，我們演算如下：
```spec
   fib2 (Suc n)
=  (fib (Suc (Suc n)), fib (Suc n))
=    {- |fib| 之定義 -}
   (fib (Suc n) + fib n, fib (Suc n))
=  (\(x,y) -> (x+y,x)) (fib2 n) {-"~~."-}
```
{.nobreak}因此我們得到
```spec
fib2 = foldN (\(x,y) -> (x+y,x)) (1,0) {-"~~."-}
```
:::
:::

```texonly
% \Exercise WRONG. Needing a different representation of |Nat|.
% 回顧：|exp b n| 計算 $b^n$;
% 在第\@ref{sec:tail-recursion-more}節中我們使用累積參數的技巧，定義下述函數
% Recall that |exp b n| computes $b^n$.
% ```spec
% expAcc :: Nat -> Nat -> Nat -> Nat
% expAcc b n x = x * exp b n {-"~~,"-}
% ```
% 由此得到了一個使用 $O(\log n)$ 個乘法計算 $b^n$ 的程式。
%
% 這次請試著把這也當作摺融合的特例：把 |exp b| 寫成 |foldN|,
% 然後試著把 |(x *) . exp b| 融合成單一的 |foldN|.
% :::{.exans}
% |exp b = foldN (b*) 1|.
%
% 嘗試將 |(x *)| 融合入 |foldN (b*) 1| 中。基底值為 |x * 1 = x|.
% 對步驟函數的要求是 |x * (b * m) = step (x * m)|.
% 由於乘法的遞移律，我們可以直接選 |step = (b *)|.
% 但為導出較快的演算法，我們分別討論 |n| 為 |Zero|, 非零偶數, 和奇數的情況。
% 當 |n := Zero|:
% ```spec
%    x * (b * Zero)
% =  x * Zero
% ```
```

## 其他資料結構 {#sec:fold-on-other-data-structures}

既然串列與自然數都有摺，其他的資料結構也可以有。

{title="二元樹"} 回顧我們提及的兩種常見二元樹：
```spec
data ITree a  = Null   | Node a (ITree a) (ITree a) {-"~~,"-}
data ETree a  = Tip a  | Bin (ETree a) (ETree a) {-"~~."-}
```
{.nobreak}其中 |ITree| 的摺可定義如下：
```haskell
foldIT :: (a -> b -> b -> b) -> b -> ITree a -> b
foldIT f e Null          = e
foldIT f e (Node x t u)  = f x (foldIT f e t) (foldIT f e u) {-"~~."-}
```
{.nobreak}內標記二元樹 |ITree| 的兩個建構元之型別分別為 |Null :: ITree a| 與 |Node :: a -> ITree a -> ITree a -> ITree a|. 和串列的摺一樣，內標記二元樹的摺將一個 |ITree a| 轉成一個型別為 |b| 的值 --- 藉由將 |Null| 代換為基底值 |e :: b|, 以及將 |Node| 代換為步驟函數 |f :: a -> b -> b -> b|.

外標記二元樹的摺則可定義如下：
```haskell
foldET :: (b -> b -> b) -> (a -> b) -> ETree a -> b
foldET f k (Tip x)    = k x
foldET f k (Bin t u)  = f (foldET f k t) (foldET f k u) {-"~~."-}
```
{.nobreak}型別 |ETree| 的建構元分別為 |Tip :: a -> ETree a| 和 |Bin :: ETree a -> ETree a -> ETree a|.
由於 |Tip| 是一個由 |a| 到 |ETree a| 的函數，取代它的得是一個型別為 |a -> b| 的*基底函數*.
取代 |Bin| 的步驟函數之型別則為 |b -> b -> b|. 有了這兩者，我們便可將 |ETree a| 轉換為 |b|.

例如，第\@ref{sec:other-inductive-datatypes}節中曾提到幾個定義在樹之上的函數：|tags| 傳回一個 |ITree| 的所有標記；|size| 傳回其大小；|minE| 傳回一個 |ETree| 的最小元素，|mapE f| 對樹中的每個標記做 |f|. 它們都可用摺定義：
```spec
tags    = foldIT (\x xs ys -> xs ++ [x] ++ ys) [] {-"~~,"-}
size    = foldIT (\x m n -> 1 + m + n) 0 {-"~~,"-}
minE    = foldET min id {-"~~,"-}
mapE f  = foldET Bin f {-"~~."-}
```
```{.haskell .invisible}
tags    = foldIT (\x xs ys -> xs ++ [x] ++ ys) [] {-"~~,"-}
size    = foldIT (\x m n -> 1 + m + n) 0 {-"~~,"-}
minE :: Ord a => ETree a -> a
minE    = foldET min id {-"~~,"-}
mapE f  = foldET Bin f {-"~~."-}
```

兩個二元樹的摺也有它們的融合定理：
:::{.theorem title="摺融合定理(|ITree|版)" #thm:fold-fusion-ITree}
\index{fold 摺!fold fusion 摺融合}
給定 |f :: a -> b -> b -> b|, |e :: b|, |h :: b -> c|, 與 |g :: a -> c -> c -> c|.
如果融合條件 |h (f x y z) = g x (h y) (h z)| 對任何 |x :: a| 與在 |foldIT f e| 值域中的 |y, z :: b| 成立，
我們有 |h . foldIT f e = foldIT g (h e)|.
```{.haskell .invisible}
foldITFusion :: (a -> b -> b -> b) -> b -> (b -> c) -> (a -> c -> c -> c) ->
                (ITree a -> c)
foldITFusion f e h g = h . foldIT f e === foldIT g (h e)
   where cond x y z = h (f x y z) === g x (h y) (h z)
```
:::

:::{.theorem title="摺融合定理(|ETree|版)" #thm:fold-fusion-ETree}
給定 |f :: b -> b -> b|, |k :: a -> b|, |h :: b -> c|, 與 |g :: c -> c -> c|.
如果融合條件 |h (f x y) = g (h x) (h y)| 對任何在 |foldET f k| 值域中的 |x, y :: b| 成立，我們有
|h . foldET f k = foldET g (h . k)|.
```{.haskell .invisible}
foldETFusion :: (b -> b -> b) -> (a -> b) -> (b -> c) -> (c -> c -> c) ->
                (ETree a -> c)
foldETFusion f k h g = h . foldET f k === foldET g (h . k)
   where cond x y = h (f x y) === g (h x) (h y)
```
:::

{.nobreak}兩個定理的融合條件都依循著與串列版相同的原則：當 |h| 與步驟函數碰在一起，融合條件讓我們將 |h| 往裡推。
兩個定理都可用單純的歸納法證明。

:::{.exlist}
:::{.exer #ex:fold-length-tags-size}
以摺融合定理證明 |length (tags t) = size t|.
:::
:::{.exans}
即證明 |length . tags = size|.
回顧 |tags = foldIT (\x xs ys -> xs ++ [x] ++ ys) []|
使用摺融合，由於 |length [] = 0| 以及
|length (xs ++ [x] ++ ys) = 1 + length xs + length ys|,
我們得到 |length . tags = foldIT (\x m n -> 1 + m + n) 0 = size|.
:::
:::{.exer #ex:foldET-mapE-fusion}
串列有 |foldr|-|map| 融合定理(\@ref{thm:foldr-map-fusion})，|ETree| 也有類似的 |foldET|-|mapE| 融合定理。請寫出該定理並證明之。
:::
:::{.exans}
|ETree| 上的 |foldET|-|mapE| 融合定理為：
```spec
  foldET f k . mapE g = foldET f (k . g) {-"~~."-}
```
{.nobreak}由於 |mapE g = foldET Bin f|, 欲證明上式可用摺融合定理。
其融合條件 |foldET f k (Bin t u) = f (foldET f k t) (foldET f k u)| 恰巧是 |foldET| 之定義。
:::
:::{.exer #ex:foldIT-mapI-fusion}
函數 |mapI :: (a -> b) -> ITree a -> ITree b| 將一個 |a -> b| 的函數作用在 |ITree| 的每一個標記上。
請用 |foldIT| 定義 |mapI|, 並寫下 |foldIT| 與 |mapI| 的融合定理並證明之。
:::
:::{.exans}
函數 |mapI| 可定義如下：
```spec
  mapI f = foldIT (\x t u -> Node (f x) t u) Null {-"~~."-}
```
{.nobreak}考慮 |foldIT f e . mapI g| 之融合。其基底值為 |foldIT f e Null = e|.
步驟函數的推導如下：
```spec
      foldIT f e (Node (g x) t u)
 ===    {- |foldIT| 之定義 -}
      f (g x) (foldIT f e t) (foldIT f e u)  {-"~~."-}
```
{.nobreak}因此 |foldIT f e . mapI g = foldIT (\x y z -> f (g x) y z) e|.
:::
:::{.exer #ex:fold-fusion-minE-mapE}
以摺融合定理證明 |minE (mapE (x +) t) = x + minE t|.
:::
:::{.exans}
即證明 |minE . mapE (x+) = (x+) . minE|.
推論如下：
```spec
      minE . mapE (x+)
 ===    {- |foldET|-|mapE| 融合，見習題 \ref{ex:foldET-mapE-fusion} -}
      foldET min (id . (x+))
 ===    {- |foldET| 融合，如下述 -}
      (x+) . minE {-"~~."-}
```
{.nobreak}融合的基底函數為 |id . (x+) = (x+) . id|,
融合條件則為 |x + (y `min` z) = (x + y) `min` (x + z)|。
:::
:::{.exer #ex:fold-ITree-append-tags}
將 |(++) . tags| 融合，以便推導出一個在線性時間內收集 |ITree| 內所有標籤的演算法。
:::
:::{.exans}
回想 |tags = foldIT (\x xs ys -> xs ++ [x] ++ ys) []|.
融合後之基底值為 |(++) [] = id|.
融合後之步驟函數 |step| 須滿足
|(++) (xs ++ [x] ++ ys) = step x (xs++) (ys++)|.
但由於左手邊的 |(++)| 還需一個參數才能化簡，我們在左右兩邊各補上一個參數 |zs|.
演算如下：
```spec
      (++) (xs ++ [x] ++ ys) zs
 ===  (xs ++ [x] ++ ys) ++ zs
 ===    {- |(++)| 之遞移律 -}
      xs ++ (x : (ys ++ zs))
 ===    {- |(.)| 之定義 -}
      ((xs++) . (x:) . (ys++)) zs {-"~~."-}
```
{.nobreak}因此我們得到 |(++) . tags = foldIT (\x f g -> f . (x:) . g) id|.
:::
:::


{title="非空串列"}
第\@ref{sec:induction-variations}節中曾提及我們可把至少有一個元素的串列想像成一個資料結構：|data ListP a = [a] || a : ListP a|. 此種串列的摺可定義為：
```haskell
foldrn :: (a -> b -> b) -> (a -> b) -> ListP a -> b
foldrn f k [x]     = k x
foldrn f k (x:xs)  = f x (foldrn f k xs) {-"~~."-}
```

:::{.example #eg:foldrn-partsP}
例\@ref{ex:partsP}中的 |partsP| 可以寫成
```haskell
partsP :: ListP a -> List (ListP (ListP a))
partsP = foldrn (\x -> concat . map (extend x)) wrap3 {-"~~,"-}
  where  extend x (ys:yss) = [[x]:ys:yss, (x:ys):yss]
         wrap3 x = [[[x]]] {-"~~."-}
```
:::

我們考慮一個定義在非空串列上的簡單演算法推導練習。
其次，這也將是一個使用 |foldrn| 與「引入脈絡」的例子，
\index{fold 摺!bringing in the context 引入脈絡}

下述函數 |ascending :: ListP Int -> Bool| 判斷一個串列是否為遞增：
```haskell
ascending [x]       = True
ascending (x:y:xs)  = x <= y && ascending (y:xs) {-"~~."-}
```
{.nobreak}給定一個整數串列，如何將它切成一個個區段，使得每個區段都是遞增的？
如果我們讓每個元素都自己成一段，似乎是滿足需求，但這沒什麼意思。
我們希望讓遞增區段盡量連續，也就是說，我們要區段數目最少的分割法。
下述函數 |upHills| 將輸入串列以最精簡的方式切成段：
```spec
upHills :: List Int -> List (List Int)
upHills = shortest . filter (all ascending) . partsP {-"~~."-}
```
{.nobreak}其中 |partsP| 把串列任意切段，|filter (all ascending)| 挑出每個區段都是遞增的分割法，而 |shortest| 挑選元素數目最少的串列。
我們能由此導出一個比較快的演算法嗎？

我們先將 |filter (all ascending)| 融入 |partsP| 之中。
經過一些稍繁瑣但原則上並不困難的計算，我們可得：
```{.haskell .invisible}
filtAscParts :: List Int -> List (List (List Int))
filtAscParts =
```
```haskell
 filter (all ascending) . partsP ===
    foldrn (\x -> concat . map (extendAsc x)) wrap3 {-"~~."-}
```
{.nobreak}這和 |partsP| 的差別只在 |extend| 變成了 |extendAsc|. 後者的定義為：
```haskell
extendAsc x (ys:yss) = if x >= head ys  then [[x]:ys:yss, (x:ys):yss]
                                        else [[x]:ys:yss] {-"~~."-}
```
{.nobreak}函數 |extendAsc| 比 |extend| 多做了一個檢查，只在 |x >= head ys| 時將 |(x:ys):yss| 列為一個可能選項。
注意：由於 |ys| 的型別是 |ListP Int|, |head| 一定可成功。
如果我們使用 |List Int|, 在這裡就得多做些條件判斷。
雖然每個非空串列 |ListP| 都可用 |List| 表達, 有些問題使用 |ListP| 描述時會比較便於證明與推論。

接著我們試圖融合 |shortest| 與 |filter (all ascending) . partsP|.
基底函數為 |(shortest . wrap3) x = shortest [[[x]]] = [[x]]|.
至於步驟函數，我們希望找到滿足下述融合條件的 |step|:
```spec
  shortest (concat (map (extendAsc x) ysss)) === step x (shortest ysss) {-"~~."-}
```
{.nobreak}由左手邊開始，由於 |shortest| 可分配進 |concat| （意即 |shortest . concat = shortest . map shortest|），我們可推論：
```spec
     shortest (concat (map (extendAsc x) ysss))
 ===   {- |shortest| 分配進 |concat|; |map| 融合 -}
     shortest (map (shortest . extendAsc x) ysss) {-"~~."-}
```
{.nobreak}為了有些進展，我們看看 |shortest . extendAsc x| 能如何化簡。
將輸入（非空串列）寫成 |ys : yss|:
```spec
      shortest (extendAsc x (ys:yss)) =
 ===    {- |extend'| 之定義; 提出 |if| -}
      if x >= head ys  then shortest [[x]:ys:yss, (x:ys):yss]
                       else shortest [[x]:ys:yss]
 ===    {- |shortest| 挑選較短之串列 -}
      if x >= head ys then (x:ys):yss else [x]:ys:yss {-"~~."-}
```
```texonly
%
%      concat (map (filter (all ascending) . extend x) ysss)
% ===  concat (map (\ (ys:yss) -> if all ascending (ys:yss) then extend' x (ys:yss) else []) ysss)
```
{.nobreak}因此，融合條件的左手邊可歸約如下：
```spec
     shortest (map (shortest . extendAsc x) ysss)
===    {- 前述推導 -}
     shortest (map (\(ys:yss) ->  if x >= head ys then (x:ys):yss
                                       else [x]:ys:yss) ysss) {-"~~."-}
```
{.nobreak}我們希望繼續將 |shortest| 往裡推，但此時似乎卡住了。


```spec
     shortest (map (\(ys:yss) ->  if x >= head (head (head ysss)) then (x:ys):yss
                                       else [x]:ys:yss) ysss) {-"~~."-}
===  shortest (  if x >= head (head (head ysss))
                 then map (\(ys:yss) -> (x:ys):yss) ysss
                 else map (\(ys:yss) -> [x]:ys:yss) ysss)
===  if x >= head (head (head ysss))
       then shortest (map (\(ys:yss) -> (x:ys):yss) ysss)
       else shortest (map (\(ys:yss) -> [x]:ys:yss) ysss)
===  if x >= head (head (head ysss))
       then (\(ys:yss) -> (x:ys):yss) (shortest ysss)
       else (\(ys:yss) -> [x]:ys:yss) (shortest ysss)
===  let (ys:yss) = shortest ysss
     in  if x >= head ys
         then (x:ys):yss else [x]:ys:yss {-"~~."-}
```

```spec
upHills = foldrn step (\x -> [[x]]) {-"~~,"-}
  where  step x (ys:yss) = if x >= head ys  then (x:ys):yss
                                            else [x]:ys:yss {-"~~."-}
```

:::{.exlist}
:::{.exer #ex:filtAscPExtend}
將 |filter (all ascending) . partsP| 融合為 |foldrn (\x -> concat . map (extendAsc x)) wrap3|, 並在過程中推導 |extendAsc| 的定義。
您可能用得上習題\@ref{ex:map-filter-split}提及的性質：
如果 |filter p (f x) = if p x then g x else []|, 則 |concat . map (filter p . f) = concat . map g . filter p|.
:::
:::{.exans}
基底函數為 |filter (all ascending) . wrap3 = wrap3|.
為求出步驟函數，我們推論：
```{.haskell .invisible}
filtAscPExtend x ysss =
```
```haskell
      filter (all ascending) (concat (map (extend x) ysss))
 ===    {- |filter p . concat = concat . map (filter p)|, |map| 融合 -}
      concat (map (filter (all ascending) . extend x) ysss)
 ===    {- 推導 |extendAsc|, 如下述 -}
      concat (map (extendAsc x) (filter (all ascending) ysss)) {-"~~,"-}
```
```{.haskell .invisible}
 where extend x (ys:yss) = [[x]:ys:yss, (x:ys):yss]
       extendAsc = extend

wrap3 x = [[[x]]]
```

欲使得最後一步成立，我們使用習題\@ref{ex:map-filter-split}中的性質，
試圖找到滿足下述條件的 |extendAsc|：
```spec
  filter (all ascending) (extend x yss) =
      if all ascending yss then extendAsc x yss else [] {-"~~."-}
```
{.nobreak}我們演算如下：
```{.haskell .invisible}
filtAscPExtendFuse :: Int -> List Int -> List (List Int) -> List (List (List Int))
filtAscPExtendFuse x ys yss =
```
```haskell
      filter (all ascending) (extend x (ys:yss))
 ===  filter (all ascending) [[x]:ys:yss, (x:ys):yss]
 ===     {- |filter| 之定義; 因 |ascending [x] = True| -}
      if all ascending (ys:yss) then
          {-"~"-}([x]:ys:yss) : filter (all ascending) [(x:ys):yss]
         else filter (all ascending) [(x:ys):yss]
 ===     {- |filter| 與 |ascending| 之定義；重安排 |if| 的幾個分支 -}
      if all ascending (ys:yss) then
           {-"~"-} if x >= head ys  then [[x]:ys:yss, (x:ys):yss]
                                    else [[x]:ys:yss]
         else []
 ===     {- 抽取出 |extendAsc| 如下 -}
      if all ascending (ys:yss) then extend' x (ys:yss) else []
```
```{.haskell .invisible}
 where extend x (ys:yss) = [[x]:ys:yss, (x:ys):yss]
```
{.nobreak}其中 |extendAsc| 的定義如下：
```haskell
extendAsc x (ys:yss) = if x >= head ys  then [[x]:ys:yss, (x:ys):yss]
                                        else [[x]:ys:yss] {-"~~."-}
```
:::
:::

## 參考資料 {#sec:folds-ref}

@GibbonsHutton:01:When
