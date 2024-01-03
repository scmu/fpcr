``` {.haskell .invisible}
{-# LANGUAGE TypeOperators #-}
module Chapters.SegProblems where

import Prelude ()
import Control.Arrow ((***))
import Data.List (inits, tails)
import Common.MiniPrelude hiding (exp, gcd)

import Chapters.Basics (square, ETree(..), ITree(..), positions, fork)
```

# 區段問題 {#ch:segment-problems}

一個串列中*連續*的任意一截被稱作一個「區段」(segment)。\index{list 串列!segment 區段}
例如，|[1,2,3]| 的區段包括|[]|,|[1]|,|[2]|,|[3]|,|[1,2]|,|[2,3]|, 以及
|[1,2,3]|本身（注意：空串列也是一個區段）。
也許因為歷史因素，許多有趣的演算法問題有這樣的形式：
給定一個串列 |xs :: List A|，一個述語 |p :: List A -> Bool|, 和一個函數 |f :: List A -> B|，我們想在 |xs| 的所有區段中，找出滿足述語 |p| 並使得 |f| 值最大的那個。
我們把這類問題統稱為「區段問題」。

本節討論一些簡單的區段問題。我們先回顧一下區段的形式定義。
第\@ref{sec:list-segments}節曾提及，下述函數 |segments| 算出一個串列的所有區段：
```haskell
segments :: List a -> List (List a)
segments = concat . map inits . tails {-"~~."-}
```
{.nobreak}其中 |tails :: List a -> List (List a)| 計算一個串列所有的後段(suffixes)，例如 |tails [1,2,3] =|
|[[1,2,3],[2,3],[3],[]]|；\index{list 串列!suffix 後段}
函數 |inits :: List a -> List (List a)| 則計算一個串列的所有前段(prefixes)，例如 |inits [1,2,3] = [[],[1],[1,2],[1,2,3]]|. \index{list 串列!prefix 前段}
對每一個後段，計算所有的前段，便得到所有的區段了。
^[我們也可以反過來，定義 |segments = concat . map tails . inits|. 本節中的所有推導與證明可調整成相對應的版本。]
事實上，如此的定義之下 |segments [1,2,3]| 會將空串列傳回很多次。
不過以本章的目的而言，我們對這些重複的 |[]| 並不在意。

為方便讀者，我們將 |inits| 與 |tails| 的歸納定義重複如下。
:::{.multicols}
::: {.mcol width="0.5\\textwidth"}
```spec
inits :: List a -> List (List a)
inits []      = [[]]
inits (x:xs)  = [] : map (x:) (inits xs) {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```spec
tails :: List a -> List (List a)
tails []      = [[]]
tails (x:xs)  = (x:xs) : tails xs {-"~~."-}
```
:::
:::

## 最大區段和 {#sec:maximum-segment-sum}

給定一個串列。請問它的眾多區段中，總和最大的和是多少？
這個*最大區段和*(*maximum segment sum*)\index{maximum segment sum 最大區段和}問題可說是最經典的區段問題。
我們可將其寫成如下的規格：
```haskell
mss :: List Int -> Int
mss = maximum . map sum . segments {-"~~,"-}
```
{.nobreak}這幾乎便是問題的字面翻譯：算出所有的區段，對每個區段算其和，然後挑出最大的一個。
^[函數 |maximum :: List Int -> Int| 的定義見例\@ref{ex:maximumP}. 我們得假設整數中有個 |-infty| 作為 |maximum []| 的結果。若要避免 |-infty|，可注意到 |inits|, |tails|, 和 |segments| 都不會傳回空串列 --- 它們的型別都可寫成更嚴格的 |ListP (List a)|。因此我們可改用例\@ref{ex:maximumP}中的 |maximumP|. 本節的推導稍加修改後即可適用。]
當輸入串列長度為 $n$, 這個定義本身是一個時間複雜度為 $O(n^3)$ 的演算法 --- 該串列的區段有 $O(n^2)$ 個，每個都需分別算總和。
我們能導出一個更快的演算法嗎？

```texonly
%format infty = "\infty"
```

{title="前段-後段分解"}許多區段問題的推導都以如下方式開頭：將 |segments| 展開成 |inits| 與 |tails|, 並將 |maximum| 往右推，與 |inits| 放在一起：
```{.haskell .invisible}
mssDer1 :: List Int -> Int
mssDer1 =
```
```haskell
      maximum . map sum . segments
 ===  maximum . map sum . concat . map inits . tails
 ===   {- |map f . concat = concat . map (map f)| (習題 \ref{ex:map-concat}) -}
      maximum . concat . map (map sum) . map inits . tails
 ===   {- |maximum . concat = maximum . map maximum| -}
      maximum . map maximum . map (map sum) . map inits . tails
 ===   {- |map| 融合 （定理\ref{thm:map-fusion}） -}
      maximum . map (maximum . map sum . inits) . tails {-"~~."-}
```
{.nobreak}細看 |maximum . map sum . inits| 這個子算式，其意思是「給定一個串列，計算其所有*前段*的和的最大值」。我們為這個子算式取個名字，令 |mps = maximum . map sum . inits|，其中 |mps| 為「最大前段和 maximum prefix sum」的縮寫。經由上述演算，我們得知
```spec
  mss = maximum . map mps . tails {-"~~,"-}
```
{.nobreak}意思是：要找出所有區段的最大和，我們可以對*每一個後段，找出其最大前段和*。

這是解許多區段問題的常見模式：要解決最佳區段問題，先試著解最佳前段問題。
要算出最佳區段，可*對每一個後段，算出其最佳前段*。
^[反過來當然也可以。如果我們定義 |segments = concat . map tails . inits|, 此處的策略就變成「對每個前段，算出其最佳後段」。]

{title="使用掃描引理"}
接下來我們注意到 |map mps . tails| 這個子算式。回顧*掃描引理*(\@ref{lma:scan-lemma}), 重複如下：
```spec
map (foldr f e) . tails = scanr f e = foldr (\x ys -> f x (head ys) : ys) [e] {-"~~."-}
```
如果我們能把 |mps| 變成一個 |foldr|，
|map mps . tails| 可改寫為 |scanr|.
如果該摺的步驟函數只花常數時間，我們就有了一個線性時間的演算法了！

如何把 |mps| 變成摺呢？由於 |inits| 是摺，我們可使用摺融合。
此處的計算和例\@ref{ex:minimumMapSumInits}很類似，我們可以把 |map sum| 與 |maximum| 分兩次融合進 |inits|, 也可以一次把 |maximum . map sum| 融合進 |inits|.
這次我們試試看後者。
基底值 |maximum (map sum [[]]) = 0|.
我們想要尋找滿足融合條件
|maxmium (map sum ([] : map (x:) xss)) = step x (maximum (map sum xss))|
的函數 |step|.
計算如下：
```{.haskell .invisible}
maxMapSumFuse :: Int -> List [Int] -> Int
maxMapSumFuse x xss =
```
```haskell
      maximum (map sum ([] : map (x:) xss))
 ===    {- |map| 與 |sum| 之定義  -}
      maximum (0 : map sum (map (x:) xss))
 ===    {- |map| 融合  -}
      maximum (0 : map (sum . (x:)) xss)
 ===    {- |sum| 之定義 -}
      maximum (0 : map ((x+). sum) xss)
 ===    {- |maximum| 之定義 -}
      0 `max` maximum (map ((x+). sum) xss)
 ===    {- |maximum . map (x+) = (x+) . maximum| -}
      0 `max` (x + maximum (map sum xss)) {-"~~."-}
```
{.nobreak}因此我們推導出了：
```{.haskell .invisible}
mpsDer00 :: List Int -> Int
mpsDer00 =
```
```haskell
      maximum . map sum . inits
 ===  maximum . map sum . foldr (\x xss -> [] : map (x:) xss) [[]]
 ===   {- 摺融合定理，融合條件如上 -}
      foldr (\x s -> 0 `max` (x + s)) 0 {-"~~."-}
```

注意：步驟函數推導的最後一步中，為了將 |maximum| 往右推，使用了如下的性質
```{.equation #eq:max-mapadd}
  |maximum . map (x+)|&|= (x+) . maximum| \mbox{~~.}
```
{.nobreak}在 \@eqref{eq:max-mapadd} 的左手邊，我們將一個串列的每個元素都加上 |x|, 然後取最大值。
性質 \@eqref{eq:max-mapadd} 告訴我們，其實我們可以先取最大值，然後做一個加法即可。
這個步驟允許我們在每一步省下了 $O(n)$ 個加法，是使得整個演算法之所以能加速的關鍵一步。
而 \@eqref{eq:max-mapadd} 的證明只需使用例行的歸納法，但其中的關鍵一步需要如下的分配律：
```{.equation #eq:plus-max}
|x + (y `max` z)| &|= (x + y) `max` (x + z)| \mbox{~~.}
```
{.nobreak}加法與|max|的分配率是使我們能有一個線性時間演算法的關鍵性質。

既然 |mps| 已經是一個摺，我們可以使用掃描引理：
```{.haskell .invisible}
mssDer01 :: List Int -> Int
mssDer01 =
```
```haskell
      maximum . map sum . segments
 ===    {- 上述計算 -}
      maximum . map (foldr (\x s -> 0 `max` (x + s)) 0) . tails
 ===    {- 掃描引理\ref{lma:scan-lemma} -}
      maximum . scanr (\x s -> 0 `max` (x + s)) 0 {-"~~."-}
```
{.nobreak}我們得到
```spec
mss = maximum . scanr (\x s -> 0 `max` (x + s)) 0 {-"~~."-}
```
{.nobreak}這是一個使用線性時間、線性空間的演算法。

藉由程式推導，我們不僅找到了一個較快的演算法，也找出了使得該演算法之所以成立的根本性質。
這使我們能輕易將該演算法推廣：不僅是加法與|max|，該演算法能用在任何滿足 \@eqref{eq:plus-max} 的一組運算元之上。

:::{.exlist}
:::{.exer #ex:max-mapadd}
證明性質 \@eqref{eq:max-mapadd}。
:::
:::

{title="常數空間"}
使用掃描引理導出的 |mss| 能在線性時間內對輸入串列的每個後段算出其 |mps| （即「最大前段和」）並存放在一個串列中。
方法是使用一個 |scanr| 將串列由右到左走訪一遍，在每一步將 |x| 與 |mps xs| 的值（存放在串列中）相加，並和 |0| 比大小。
每個 |mps| 值之中最大的那個，便是我們要的答案。
在函數語言圈內，關於最大區段和的討論大多到此為止：我們已經有了一個漂亮的線性時間演算法了。

若要再挑惕，這個演算法的不盡滿意之處是需要線性的空間 --- |scanr| 會產生一個中間串列，由 |maximum| 消掉。
我們有可能把 |maximum| 與 |scanr| 融合，得到一個不產生中間串列的演算法嗎？根據摺融合定理，我們將需要找到滿足以下融合條件的函數 |step|：
```spec
 maximum (0 `max` (x + head ys) : ys) = step x (maximum ys) {-"~~."-}
```
{.nobreak}這顯然做不到：從 |maximum ys| 是無法取出 |head ys| 的。


這時就用得上*組對*的技巧了 --- 既然需要 |head|，就把它一併歸納地算出來吧！
定義：
```{.haskell .invisible}
maxhd xs = (maximum xs, head xs)
```
```spec
  msps = fork maximum head . scanr (\x s -> 0 `max` (x + s)) 0 {-"~~."-}
```
{.nobreak}要把 |fork maximum head| 融入 |scanr|, 我們依融合條件推導：
```spec
     fork maximum head (0 `max` (x + head ys) : ys)
===    {- |fork| 之定義 -}
     (maximum (0 `max` (x + head ys) : ys), head (0 `max` (x + head ys) : ys))
===    {- |maximum| 與 |head| 之定義 -}
     ((0 `max` (x + head ys)) `max` maximum ys, 0 `max` (x + head ys))
===    {- 取出 |(maximum ys, head ys)| -}
     (\m s -> ((0 `max` (x + s)) `max` m, 0 `max` (x + s))) (maximum ys, head ys)
===    {- 取出重複項 |0 `max` (x + s)| -}
     (\m s -> let s' = 0 `max` (x + s) in (s' `max` m, s')) (maximum ys, head ys)  {-"~~."-}
```
{.nobreak}我們得到
```texonly
%{
%format mss'' = mss
```
```spec
mss'' = fst . msps {-"~~,"-}

msps :: List Int -> (Int :* Int)
msps = foldr (\m s -> let s' = 0 `max` (x + s) in (s' `max` m, s')) (0,0) {-"~~."-}
```
{.nobreak}或著，我們把 |msps| 的 |foldr| 定義展開，也許比較容易理解：
```{.haskell #code:msps}
msps []      =  (0,0)
msps (x:xs)  =  let  (m,s) = msps xs
                     s' = 0 `max` (x + s)
                in   (s' `max` m, s') {-"~~."-}
```
```texonly
%} %mss''
```
{.nobreak}這是一個使用線性時間、常數空間計算最大區段和的演算法。當 |(m,s) = msps xs|, |m| 是 |xs| 的最大區段和，|s| 則是 |xs| 的最大前段和。
每考慮一個新元素 |x|, 最大前段和被更新為 |0 `max` (x + s)| --- 如果把 |x| 接上後仍是正數，|x+s| 就是最好的前段和，否則最大前段和是空串列的和 |0|.
新的最大前段和再與 |m| 比較，得到新的最大區段和。


:::{.infobox title="指令式版本的最大區段和"}
```texonly
%{
%format x0
%format xN1 = "\Varid{x}_{N-1}"
%format do = "\mathbf{do}"
%format od = "\mathbf{od}"
```
根據第\@ref{sec:tail-recursion}節的討論，當輸入串列|[x0..xN1]| 被逆向存放在陣列 |X| 之中，函數 |msps| 相當於以下的指令式程式：
```{.spec #code:mss:imperative}
i, m, s := 0, 0, 0;
do i /= N ->  s := 0 `max` (X i + s) ;
              m := m `max` s ;
              i := i + 1
od ;
return m
```
{.nobreak}這在指令式程式推導的領域中也是一個經典範例。
```texonly
%} %GCL
```
:::


## 最長高原問題 {#sec:maximum-plateau-length}

```texonly
%format initsP = "\Varid{inits}^{+}"
%format tailsP = "\Varid{tails}^{+}"
%format segmentsP = "\Varid{segments}^{+}"
```

如果一個區段的每個元素都相等，我們稱之為一個「高原(plateau)」。
本節考慮這個問題：給一個串列，找出其中最長的高原的長度。
例如當輸入為 |[2,3,3,2,2,2,1,6,6]| 時，輸出應為 |3| --- 即最長的高原 |[2,2,2]| 的長度。
以下是本問題的一種可能的規格寫法：
```haskell
lp :: List Int -> Int
lp = maximum . map length . filter plateau . segmentsP {-"~~,"-}
```
{.nobreak}其中 |segmentsP| 算出所有的區段，|plateau| 判斷一個區段是否為高原。
過濾出所有的高原後，我們計算每個高原的長度，然後找出最大值。
^[函數 |lp| 與 |plateau| 可以有更通用的型別 |Eq a => List a -> Int|, |Eq a => List a -> Bool|.]

函數 |segmentsP| 和 |segments| 類似，其定義為：
```haskell
segmentsP :: List a -> List (ListP a)
segmentsP = concat . map initsP . tailsP {-"~~,"-}
```
{.nobreak}函數 |initsP| 與 |tailsP| 則與 |inits| 與 |tails| 類似，但只傳回非空的前後段，定義如下：
::: {.multicols}
::: {.mcol width="0.5\\textwidth"}
```haskell
initsP :: List a -> List (ListP a)
initsP []      = []
initsP (x:xs)  = [x] : map (x:) (initsP xs) {-"~,"-}

```
:::
::: {.mcol width="0.5\\textwidth"}
```haskell
tailsP :: List a -> List (ListP a)
tailsP []      = []
tailsP (x:xs)  = (x:xs) : tailsP xs {-"~~."-}
```
:::
:::
以上三個函數的回傳型別都是 |List (ListP a)| ---
每個傳回的前/後/區段都是非空的，但並非每個串列都有非空的前/後/區段。
函數 |lp| 仍可接受空串列作為輸入，但（我們等下將看到）在規格中使用 |segmentsP| 將帶來不少方便。
我們也可使用 |segments| 定最長平原問題的規格，只是會增加一些不利於講解的細節。

函數 |plateau| 可定義如下：
```haskell
plateau :: ListP Int -> Bool
plateau [x]       = True
plateau (x:y:xs)  = x == y && plateau (y:xs) {-"~~."-}
```
{.nobreak}由於輸入是非空串列，|plateau| 的定義中考慮的是「有一個元素」和「有兩個以上元素」的兩種情況。

:::{.infobox title="區段問題不傳回區段？"}
為何我們在最大區段和問題中只傳回最大區段的和、在最長高原問題中只傳回長度，而不傳回該區段本身呢？

\quad 這是許多演算法題目常見的簡化：當真正的問題是尋找「使得某值最大的聚合資料結構」時，我們常只要求解題者傳回該值，而不是整個聚合資料結構。如此做的好處之一是讓我們能暫時忽略「如何組出需傳回的資料結構」的細節，更專注在問題本身。這使得問題的規格與推導過程都簡單許多。

\quad 如果我們真的需要整個區段，我們總能將前述的簡單版程式擴充為傳回資料結構的程式。讀者不妨試試能否將第 \@pageref{code:mpsAll} 頁的 |mpsAll| 改寫為型別為
|List Int -> List (Int :* List Int)| 的程式 --- 對每個後段，計算其*最佳前段和，以及該前段*。您會發現程式結構並沒有改變，只是多了些繁瑣的細節。

\quad 另一個理由是：具有最大和的區段可能不只一個。在*函數*程式推導之中，如果我們要傳回區段，由於規格也是函數，我們似乎必須在規格中就決定傳回哪一個。若希望規格是「傳回*任一個*具有最大和的區段」，我們會需要更多機制，例如使用*關係*(*relation*)或使用單子。
:::

{title="前段-後段分解"}
和最大區段和問題一樣，我們先嘗試把這個區段問題分解為「對每個後段，計算最佳前段」：
```{.haskell .invisible}
lppDer1 :: List Int -> Int
lppDer1 =
```
```haskell
      maximum . map length . filter plateau . segmentsP
 ===  maximum . map length . filter plateau . concat . map initsP . tailsP
 ===     {- 因 |filter p . concat = concat . map (filter p)| -}
      maximum . map length . concat . map (filter plateau . initsP) . tailsP
 ===     {- 因  |map f . concat = concat . map (map f)|, |map| 融合 -}
      maximum . concat . map (map length . filter plateau . initsP) . tailsP
 ===     {- 因 |maximum . concat = maximum . map maximum|, |map| 融合 -}
      maximum . map (maximum . map length . filter plateau . initsP) . tailsP {-"~~."-}
```

{title="嘗試使用掃描引理"}
下一步：我們把 |maximum . map length . filter plateau . initsP| 簡寫為 |lpp|，
並嘗試將它寫成 \@eqref{eq:f-fold-scan} 的形式，以便使用掃描引理。演算如下：
```{.haskell .invisible}
lppDer2 :: Int -> List Int -> Int
lppDer2 x xs =
```
```haskell
      (maximum . map length . filter plateau . initsP $ (x:xs))
 ===  (maximum . map length . filter plateau $ [x] : map (x:) (initsP xs))
 ===    {- |filter| 之定義，|plateau [x] = True| -}
      maximum (1 : map length (filter plateau (map (x:) (initsP xs))))
 ===  1 `max` maximum (map length (filter plateau (map (x:) (initsP xs)))) {-"~~."-}
```
```texonly
%format &&: = "\mathbin{\dot{\wedge}}"
```

演算至此的問題是：如何把 |map (x:)| 提出來呢？
定理\@ref{thm:filter-map}允許我們把 |map| 搬到 |filter| 的左邊：
```spec
 filter p . map f = map f . filter (p . f) {-"~~."-}
```
{.nobreak}至於 |plateau . (x:)| 能否再化簡？觀察 |plateau| 定義的第二個子句：
```spec
plateau (x:y:xs)  = x == y && plateau (y:xs) {-"~~,"-}
```
{.nobreak}寫成函數組合的形式便是：
```spec
plateau . (x:) = ((x ==) . head) &&: plateau {-"~~,"-}
```
{.nobreak}其中 |(&&:)| 為「提升成函數版」的 |(&&)|, 定義為
```haskell
(&&:) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(f &&: g) x = f x && g x {-"~~."-}
```
{.nobreak}函數 |(&&) :: Bool -> Bool -> Bool| 拿兩個布林值、算出一個新布林值，|(&&:)| 則拿兩個函數 |f, g :: a -> Bool|，組合成另一個型別為 |a -> Bool| 的函數，其結果是 |f| 與 |g| 之傳回值的合取。函數 |filter| 與 |(&&:)| 有如下的性質：
```{.equation #eq:filter-conjunct}
  |filter (p &&: q)| & |= filter p . filter q| \mbox{~~.}
```
{.nobreak}有了以上眾多性質，我們演算如下：
```{.haskell .invisible}
lppDer3 :: Int -> List (List Int) -> List (ListP Int)
lppDer3 x =
```
```haskell
      filter plateau . map (x:)
 ===    {- 定理 \ref{thm:filter-map} -}
      map (x:) . filter (plateau . (x:))
 ===    {- |plateau| 之定義 -}
      map (x:) . filter (((x ==) . head) &&: plateau)
 ===    {- 因 \eqref{eq:filter-conjunct}: |filter (p &&: q) = filter p . filter q| -}
      map (x:) . filter plateau . filter ((x ==) . head) {-"~~."-}
```
{.nobreak}現在整個式子成為 |1 `max` (maximum . map (length . (x:)) . filter plateau . filter ((x ==) . head) . initsP) $ xs|.

把 |map (x:)| 往左搬之後，式子的右邊出現了 |filter ((x ==) . head) (initsP xs)| --- 產生所有 |xs| 的非空前段，取出第一個元素為 |x| 的。但讀者們可能立刻發現：|initsP| 傳回的每個前段的第一個元素都是一樣的！也就是說我們有以下性質。
```texonly
\begin{flalign}
\qquad\quad
\begin{split}
&  |filter ((x==) . head) (initsP xs) =|\\
&\qquad   |if x == head xs then initsP xs else [] {-"~~."-}|
\end{split} &
\label{eq:initsP-heads}
\end{flalign}
```
考慮非空前段的好處在這兒可看出：|head| 對非空串列才有值。

回到 |lpp|，我們可繼續推導如下：
```{.haskell .invisible}
lppDer4 :: Int -> List Int -> Int
lppDer4 x xs =
```
```haskell
      lpp (x : xs)
 ===   {- 前述演算, |map| 融合 -}
      1 `max`  (maximum . map (length . (x:)) . filter plateau .
                  filter ((x ==) . head) . initsP $ (x : xs))
 ===   {- 因 \eqref{eq:initsP-heads} -}
      1 `max`  (maximum . map (length . (x:)) . filter plateau $
                  if x == head xs then initsP xs else [])
 ===   {- \eqref{eq:fn-if-distribute}: 函數分配進 |if| -}
      if x == head xs
        then 1 `max`  (maximum . map (length . (x:)) . filter plateau . initsP $ xs)
        else 1 `max` (maximum . map (length . (x:)) . filter plateau $ [])
 ===   {- |length . (x:) = (1+) . length|, 及其他化簡 -}
     if x == head xs
        then 1 + (maximum . map length . filter plateau . initsP $ xs)
        else 1
 ===   {- |lpp| 之定義 -}
     if x == head xs then 1 + lpp xs else 1 {-"~~."-}
```
{.nobreak}由此我們得到
```haskell
lpp [x]     = 1
lpp (x:xs)  = if x == head xs then 1 + lpp xs else 1 {-"~~."-}
```
{.nobreak}然而，我們雖為 |lpp| 推導出了一個歸納定義，該定義並不符合 \@eqref{eq:f-fold-scan}！
後者要求 |lpp| 的右手邊必須是 |x `oplus` lpp xs| 的形式 --- 在 |lpp xs| 之外不能有其他的 |xs|, 而上述的 |lpp| 右手邊多了一個 |head xs|.

這時組對的技巧又派上用場了。定義：
```spec
lpph xs = (lpp xs, head xs) {-"~~,"-}
```
{.nobreak}我們可推導出
```haskell
lpph [x]     = (1, x)
lpph (x:xs)  = (if x == y then 1 + n else 1, x) {-"~~,"-}
   where (n,y) = lpph xs {-"~~."-}
```
{.nobreak}該函數符合 \@eqref{eq:f-fold-scan} 的形式，其中 |e = (1,x)|, |x `oplus` (y,n) = (if x == y then 1 + n else 1, x)|.

{title="總結"}
綜合目前為止的推導，函數 |lpp| 的推導大架構如下：
```{.haskell .invisible}
lppDer5 :: Int -> List Int -> Int
lppDer5 x =
```
```haskell
      lpp
 ===    {- 前段-後段分解 -}
      maximum . map (maximum . map length . filter plateau . initsP) . tailsP
 ===    {- 前述演算：尋找歸納定義 -}
      maximum . map lpp . tailsP
 ===    {- 因 |lpp = fst . lpph|  -}
      maximum . map (fst . lpph) . tailsP
 ===    {- 掃描引理 -}
      maximum . map fst . lpphAll {-"~~,"-}
```
{.nobreak}其中 |lpphAll| 的定義如下：
```haskell
lpphAll [x]     = [(1,x)]
lpphAll (x:xs)  = (if x == y then 1 + n else 1, x) : (n,y) : ys {-"~~,"-}
  where ((n,y) : ys) = lpphAll xs {-"~~."-}
```
{.nobreak}這是一個使用線性時間、線性空間的演算法。

## 參考資料 {#sec:segProblems-ref}

{title="最大區段和"} 對試圖推銷程式推導的人來說，最大區段和問題幾乎有模範問題該有的一切特質：
目標不難理解，但又不容易一眼看出怎麼解得快；
大部分的推導過程都能用很形式化、依符號推導的方式進行；
推出的程式有顯著的效率提升。程式僅需短短幾行，乍看之下卻不容易理解為何會正確。
因此最大區段和問題是程式推導圈內常常提及的經典例子。

根據 Bentley 的 *Programming Pearls*[@Bentley:86:Programming] 一書，
最大區段和問題最初由 Brown 大學的 Ulf Grenander 所提出。
他當時正設計一個圖形配對的函式。
其中，具有最大區段和的*二維*子陣列是圖形中最有可能含有指定樣式的區域。
二維問題比較難解，因此他先考慮一維的情況：

> 1977 年，[Grenander] 把該問題講給 UNILOGIC 公司的 Michael Shamos 聽，
後者一夜之間就設計出了**演算法3**.
> Shamos 不久後告訴我這個問題時，我們都認為那大概就是最好的解法了；...
> 又幾天後，Shamos 在 Carnegie-Mellon 大學的專題討論會中講了這個問題和它的來龍去脈。
> 當時在場的統計學家 Jay Kadane 一聽，幾分鐘內就設計出了**演算法4**.

> --- Jon Bentley, *Programming Pearls* (第一版), 第76頁.

Kadane 的**演算法4**就是現在廣為人所知的（指令語言版）線性時間解（見第\@pageref{code:mss:imperative}頁）。

Shamos 的**演算法3**則是一個採取*分而治之*(*divide and conquer*)法的演算法：
將陣列分成長度略等的兩半|xs ++ ys|, 分別計算 |xs| 與 |ys| 的最大區段和。
但除此之外，還得考慮跨越 |xs| 與 |ys| 的區段。
因此該演算法在遞迴的每一層又多用了兩個迴圈，分別計算 |xs| 的最大後段和與 |ys| 的最大前段和，
兩者之和就是橫跨 |xs| 與 |ys| 的最大區段和。
（見第\@pageref{code:mss:shamos}頁。）
該演算法使用 $O(n \log n)$ 的時間。

事後回顧，Shamos 其實不需在每層都把最大前段與後段和重頭算起。
我們可用類似組對的想法，對每個子陣列都由下至上地算出以下四個值：最大前段和、最大區段和、最大後段和，以及總和。
如此一來我們可得到一個線性時間演算法。
這可看作給我們的一個暗示：「分而治之」在此也許是不必要的，我們不需要把陣列從中切半。
事實上，把陣列分成頭與尾反而讓事情簡化不少。
Kadane 立刻想出了**演算法4**，不知是否用了同樣的思路？

我最初是在 @Gibbons:97:Calculating 中見到此問題，當時便覺得印象深刻。
Gibbons 的這篇文章是很好的函數程式推導簡介。
@Bird:96:Generic 改用*關係* --- 函數的一種擴充 --- 解最大區段和問題，並推廣到其他資料結構。
@Mu:08:Maximum 則以最大區段和問題為開端，討論一些有趣的變形：例如有長度限制的最大區段和，和最大*平均*區段。

:::{.infobox title="Shamos 的最大區段和演算法"}
以下是我根據個人理解將 Shamos 的**演算法3**寫成的 Python 程式。
```texonly
%{
%format def = "\mathbf{def}"
%format for = "\mathbf{for}"
```
```{.spec #code:mss:shamos}
def mss(l,u):

  if l > u:
    return 0               {-"\quad\color{burntorange}{\mbox{\# 空陣列的情況}}"-}
  else if l == u:
    return (0 `max` a[l])  {-"\quad\color{burntorange}{\mbox{\# 單一元素陣列的情況}}"-}
  else:
    m = (l + u) / 2


    {-"\color{burntorange}{\mbox{\# 計算 a[l..m] 的最大後段和}}"-}
    sum, maxToLeft = 0, 0
    for i in range (m, l-1, -1):
      sum = sum + a[i]
      maxToLeft = maxToLeft `max` sum


    {-"\color{burntorange}{\mbox{\# 計算 a[m+1..u] 的最大前段和}}"-}
    sum, maxToRight = 0, 0
    for i in range (m+1, u+1):
      sum = sum + a[i]
      maxToLeft = maxToRight `max` sum


    maxCrossing = maxToLeft + maxToRight


    {-"\color{burntorange}{\mbox{\# 遞迴計算 a[l..m] 與 a[m+1..u] 的最大區段和}}"-}
    maxInL = mss(l,m)
    maxInR = mss(m+1,u)


    return (maxInL `max` maxCrossing `max` maxInR)
```
```texonly
%}
```
:::

{title="區段問題"}
@Zantema:92:Longest
