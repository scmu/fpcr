``` {.haskell .invisible}
{-# LANGUAGE TypeOperators #-}
module Chapters.Derivation where

import Prelude ()
import Control.Arrow ((***))
import Data.List (inits, tails)
import Common.MiniPrelude hiding (exp, gcd)

import Chapters.Basics (square, ETree(..), ITree(..), positions, fork)
import Chapters.Induction (mapI, sublists)
import qualified Chapters.Induction as Induction
```

# 一般程式推導 {#ch:derivation}

*程式推導*(*program derivation*)\index{program derivation 程式推導}是本書的重要主題。
給定一個待解決的問題，並假設該問題能描述成邏輯、數學、或其他形式語言（稱作一個形式規格(specification)），
程式推導泛指*以嚴謹方式將該規格轉換成一個解決該問題的程式*的方法。
指令式語言與函數語言都能做程式推導，而且有許多道理可相通。
本書討論函數語言的程式推導。
一個簡單、典型的函數程式語言推導可能有如下的形式：
```texonly
%{
%format en = "\Varid{e}_{\Varid{n}}"
```
```spec
  spec
=  {- 性質 1 -}
  e1
=  {- 性質 2 -}
  ....
=  {- 性質 n -}
  en {-"~~."-}
```
{.nobreak}其中 |spec| 是問題的規格，通常也是一個函數語言程式。
根據性質 1, |spec| 等於 |e1|；根據性質 2，|e1| 等於 |e2|... 長此以往，直到我們導出一個符合我們要求的 |en|.
光這麼看來，這和我們前幾章作的數學證明似乎沒什麼不同。
差別在於，做證明時我們已有 |spec| 和 |en|，要做的是把 |spec| 到 |en| 之間的步驟補足。
但做程式推導時，我們是從 |spec| 出發，希望透過種種跡象找出一個滿意的（可能是夠快的、不佔空間的、或滿足某些其他性質的）|en|.
當然，找出 |en| 之後，從 |spec| 推出 |en| 的過程就成了 |spec = en| 的證明。
當程式推導的進行方式類似數學演算，有人可能稱之為*程式演算*(*program calculation*)\index{program calculation 程式演算}。
本書混用這兩個詞彙，並不區分。

為何做程式推導？第一個理由是我們希望程式正確。
此處「正確」指的是 |en| 確實滿足了最初的規格 |spec|。但如果只為了正確性，我們為何不能先無論如何把 |en| 寫出，再試著證明 |spec = en|？
原因之一是通常程式寫好了，大家便不想證它了。
更重要的是：程式開發時，若沒有把「怎麼證明它」列入考量，寫出的程式常常是很難證明的。
為了確保有證明，最好讓「產生證明」這件事成為程式開發過程的一部分，甚至讓證明引導程式的開發。
Dijkstra 說道：

>  先給一個程式再證明它，在某個意義上是把馬車放在馬前面。
>  更有希望的做法是讓正確性證明與程式一起長出來：
>  如此一來，我們能選擇證明的結構，然後設計一個能用這種方法證明出來的程式。
>  這還有個額外的好處：正確性考量可以成為程式該怎麼寫的引導與啟發。[@Dijkstra:74:Programming]

```texonly
   % to prove the correctness of a given program, was in a sense putting the cart before the horse. A much more promising approach turned out to be letting correctness proof and program grow hand in hand: with the choice of the structure of the correctness proof one designs a program for which this proof is applicable. The fact that then the correctness concerns turn out to act as an inspiring heuristic guidance is an added benefit.\cite{Dijkstra:74:Programming}
```
Dijkstra 的最後一句話帶到了程式推導的第三個理由：
提倡者認為，程式推導的種種方法與技巧可以引導我們去分析、思考、解決問題；
這是解問題、甚至發現新演算法的方法（@Backhouse:03:Program, @Backhouse:11:Algorithmic）。
藉由良好的符號設計，我們可以發現常見的程式推導模式，並將其推廣到其他有類似性質的問題上。
```texonly
%} % format en
```

第\@ref{ch:intro}章的結尾說道「函數語言的價值便是：它是個適於演算的語言。」
便於做程式推導，是我覺得函數語言最突出的特質。
我們可以由規格出發、在符號上操作，將程式如同求代數的解一樣地算出來。只要每個小步驟都正確，最後的程式就是正確的。
由第\@ref{ch:basics}章至今，我們做了許多準備工作，備齊需要的基本知識。現在我們終於可以開始做一些演算了。


## 展開-收回轉換 {#sec:fold-unfold-transform}

考慮這麼一個例子：給定一個整數形成的串列，我們想計算其每個數的平方的和。例如當輸入是|[2,6,5,3]|, 我們希望算出 $2^2 + 6^2 + 5^2 + 3^2 = 74$. 這項工作可以簡短地描述如下：
```texonly
\begin{flalign}
\qquad\quad
|sumsq| &|= sum . map square {-"~~."-}| &
\label{eq:sumsq-oneliner}
\end{flalign}
```
```{.haskell .invisible}
sumsq :: List Int -> Int
sumsq = sum . map square
```
函數 |sumsq| 的型別為 |List Int -> Int|.
其中 |map square| 將輸入串列的每個元素都平方，然後由 |sum| 計算其總和。第\@ref{sec:induction-lists}節中給過一個 |sum| 的歸納定義，重複如下：
```spec
sum :: List Int -> Int
sum []      = 0
sum (x:xs)  = x + sum xs {-"~~."-}
```

{title="消除中間串列"}
對大部分的應用而言，如上定義的 |sumsq| 已經很堪用了。但作為一個例子，我們來挑惕些仍不滿意之處。執行 |sumsq xs| 時，|map square| 會產生另一個（存放 |xs| 每個元素的平方的）串列，該串列隨即由 |sum| 消掉 --- 感覺上似乎很浪費空間與時間。
^[在惰性求值的情況下，該中間串列的*每個*節點被產生後立刻被 |sum| 消去，因此不會真的佔用和 |xs| 同樣長度的空間。這也是大家覺得惰性求值有助於模組化、使小函數變得易於重用的例子之一。但「產生一個新節點、立刻消去」仍耗了一些不必要的時間。]
有不產生這個中間串列的方法嗎？

我們試著做些計算。當 |sumsq| 的參數是 |[]| 時：
```{.haskell .invisible}
sumsqDer0 :: Int
sumsqDer0 =
```
```haskell
   sumsq []
 ===    {- |sumsq| 之定義 -}
   sum (map square [])
 ===    {- |map| 之定義 -}
   sum []
 ===    {- |sum| 之定義 -}
   0 {-"~~."-}
```
{.nobreak}由此我們得知 |sumsq []| 會被計算成 |0|. 當輸入不是空串列時呢？試計算：
```{.haskell .invisible}
sumsqDer1 :: Int -> List Int -> Int
sumsqDer1 x xs =
```
```haskell
   sumsq (x:xs)
 ===    {- |sumsq| 之定義 -}
   sum (map square (x:xs))
 ===    {- |map| 之定義 -}
   sum (square x : map square xs)
 ===    {- |sum| 之定義 -}
   square x + sum (map square xs)
 ===    {- |sumsq| 之定義 -}
   square x + sumsq xs {-"~~."-}
```
{.nobreak}可得知對任何 |x| 與 |xs|, |sum (x:xs)| 歸約的結果和 |square x + sumsq xs| 會是相同的。
總結說來，藉由計算，我們發現 |sumsq| 滿足以下兩條性質：
```texonly
\begin{flalign}
\qquad\quad
\begin{split}
|sumsq []|      &|= 0| \\
|sumsq (x:xs)|  &|= square x + sumsq xs {-"~~."-}|
\end{split} &
\label{eq:sumsq-inductive}
\end{flalign}
```

但如果我們翻轉過來，把這兩條性質當作 |sumsq| 的新定義呢？
這是一個依據歸納法定義的良好程式，而且不會產生中間串列！

但我們怎知道 |sumsq| 的新定義滿足我們最初的要求 \@eqref{eq:sumsq-oneliner}，即 |sumsq = sum . map square| 呢？
回顧起來，我們的演算只證明了當 |sumsq| 滿足 \@eqref{eq:sumsq-oneliner}，它也滿足 \@eqref{eq:sumsq-inductive}，
卻還不能據此宣稱另一個方向：若 \@eqref{eq:sumsq-inductive} 成立，\@eqref{eq:sumsq-oneliner} 也成立。
我們將在第\@ref{ch:semantics}章詳細討論這個問題。
目前可暫時這麼說：如果我們從某個問題規格 |f = e| 起始，發現 |f| 滿足某一組等式，而這些等式剛好可湊成一個*會正常終止*的歸納定義，則 |e| 確實是唯一滿足這些等式的解。由於如此的 |e| 是唯一的，我們也可倒過來以這組等式為 |f| 的定義，並同時宣稱 |f = e| 這個性質成立。

回顧起來，在 |sumsq| 的計算中，我們僅是把 |sumsq| 的定義展開，接著展開 |map|, |sum| 等等元件的定義，直到我們又看到 |sumsq| 的定義出現在式子中、剛好可以收回為止。
這是一種單純而歷史悠久的程式推導方法，稱作*展開-收回轉換*(*fold-unfold transformation*)\index{fold-unfold transformation 展開-收回轉換}。
雖然簡單，有時這個方法意外地有用。

在這個例子中，我們真正做到的是將一個單行、使用全麥編程的 |sumsq| 定義轉換成了一個歸納定義。
新定義的 |sumsq| 比起原版稍有效率些，但這只是恰巧發生的 --- 歸納定義的程式不見得總會比較有效率。
程式推導確保程式的正確性 --- 意即*導出的程式與原本的規格是同一個函數*。
但新程式的效率仍須單獨分析。這是下一節的主題。

```texonly
% ```haskell
% pos :: Eq a => a -> List a -> Int
% pos x = length . takeWhile (x /=) {-"~~."-}
% ```
%
% %if False
% ```haskell
% posDer1 =
% ```
% %endif
% ```haskell
%       pos x (y:ys)
%  ===    {- |pos| 之定義 -}
%       length (takeWhile (x /=) (y : ys))
%  ===    {- |takeWhile| 之定義 -}
%       length (if x /= y  then y : takeWhile (x /=) ys else [])
%  ===    {- \eqref{eq:fn-if-distribute}, |length| 之定義 -}
%       if x /= y  then Suc (length (takeWhile (x /=) ys)) else Zero
%  ===    {- |pos| 之定義 -}
%       if x /= y  then Suc (pos x ys) else Zero {-"~~."-}
% ```
% ```spec
% pos :: Eq a => a -> List a -> Int
% pos x []      =
% pos x (y:ys)  = if x /= y  then Suc (pos x ys) else Zero {-"~~."-}
% ```
```

:::{.exlist}
:::{.exer #ex:descend}
下述函數 |descend n| 傳回 |[n, n-1, n-2...0]|:
```haskell
descend :: Nat -> List Nat
descend Zero     = []
descend (Suc n)  = Suc n : descend n {-"~~."-}
```
{.nobreak}定義 |sumseries = sum . descend|.
請找出 |sumseries| 的歸納定義。
:::
:::{.exans}
顯然 |sum (descend 0) = 0|. 考慮歸納情況：
```{.haskell .invisible}
sumDescendDer1 :: Nat -> Nat
sumDescendDer1 n =
```
```haskell
   sum (descend (Suc n))
 ===   {- |descend| 之定義 -}
   sum (Suc n : descend n)
 ===   {- |sum| 之定義 -}
   (Suc n) +: sum (descend n)
 ===   {- |sumseries| 之定義 -}
   (Suc n) +: sumseries n {-"~~."-}
```
{.nobreak}因此
```haskell
sumseries Zero     = Zero
sumseries (Suc n)  = (Suc n) +: sumseries n {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:repeatN}
承接習題\@ref{ex:descend}。函數 |repeatN :: (Nat :* a) -> List a| 的定義為
```spec
repeatN (n,x) = map (const x) (descend n) {-"~~."-}
```
{.nobreak}因此，|repeatN (n,x)| 會傳回一個含 |n| 個 |x| 的串列。
例如 |repeatN (3,'a') = "aaa"|.
請算出一個歸納定義的 |repeatN|.
:::
:::{.exans}
顯然 |repeatN (0,x) = []|.
至於歸納情況，演算如下：
```{.haskell .invisible}
repeatNDer1 :: Nat -> a -> List a
repeatNDer1 n x =
```
```haskell
   repeatN (Suc n, x)
 ===   {- |repeatN| 之定義 -}
   map (const x) (descend (Suc n))
 ===   {- |descend| 之定義 -}
   map (const x) (Suc n : descend n)
 ===   {- |map| 與 |const| 之定義 -}
   x : map (const x) (descend n)
 ===   {- |repeatN| 之定義 -}
   x : repeatN (n,x) {-"~~."-}
```
{.nobreak}因此，
```haskell
repeatN (Zero,   x)  = []
repeatN (Suc n,  x)  = x : repeatN (n,x) {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:rld}
承接習題\@ref{ex:repeatN}。遊程編碼(run-length encoding)\index{run-length encoding 遊程編碼}是一種簡單的壓縮方式：將字串中重複的字元表達成其出現的數字。例如 |"aaabbbbcdd"| 可以表達為 |"3a4b1c2d"|. 下列函數 |rld :: List (Nat :* a) -> List a| 則是抽象過的「遊程解碼」，將已經表示成（次數$\times$字元）的壓縮文展開：
```spec
rld = concat . map repeatN {-"~~."-}
```
{.nobreak}例如， |rld [(2,'a'), (3,'b'), (1,'c')] = "aabbbc"|.
請導出 |rld| 的歸納定義。
:::
:::{.exans}
基底狀況：
```spec
   rld []
=    {- |rld| 之定義 -}
   concat (map repeatN [])
=    {- |map| 與 |concat| 之定義 -}
   [] {-"~~."-}
```
{.nobreak}歸納狀況：
```{.haskell .invisible}
rldDer1 :: Nat -> a -> List (Nat, a) -> List a
rldDer1 n x xs =
```
```haskell
      rld ((n,x):xs)
 ===    {- |rld| 之定義 -}
      concat (map repeatN ((n,x):xs))
 ===    {- |map| 之定義 -}
      concat (repeatN (n,x) : map repeatN xs)
 ===    {- |concat| 之定義 -}
      repeatN (n,x) ++ concat (map repeatN xs)
 ===    {- |rld| 之定義 -}
      repeatN (n,x) ++ rld xs {-"~~."-}
```
{.nobreak}因此我們已推導出：
```haskell
rld []          = []
rld ((n,x):xs)  = repeatN (n,x) ++ rld xs {-"~~."-}
```
:::
:::

```texonly
% :::{.exer #ex:pos-length-takeWhile}
% There is another way to define |pos| such that
% |pos x xs| yields the index of the first occurrence of |x| in |xs|:
% ```spec
% pos :: Eq a => a -> List a -> Int
% pos x = length . takeWhile (x /=) {-"~~."-}
% ```
% (This |pos| behaves differently from the one in the lecture when
% |x| does not occur in |xs|.) Construct an inductive definition
% of |pos|.
```

:::{.exlist}
:::{.exer #ex:delete-select}
下列函數 |delete| 將輸入串列中的每個元素輪流刪除：
```haskell
delete         ::  List a -> List (List a)
delete []      =   []
delete (x:xs)  =   xs : map (x:) (delete xs) {-"~~,"-}
```
{.nobreak}例如，|delete [1,2,3,4] = [[2,3,4], [1,3,4], [1,2,4], [1,2,3]]|.
函數 |select :: List a -> List (a :* List a)| 則將一個串列中的元素依次選出。
例如，|select [1,2,3,4] = [(1,[2,3,4]), (2,[1,3,4]), (3,[1,2,4]), (4,[1,2,3])]|. 函數 |select| 恰巧可用 |delete| 定義出來：
```haskell
select xs = zip xs (delete xs) {-"~~."-}
```
{.nobreak}請推導出 |select| 的歸納定義。**提示**：下述性質可能有用 ---
|zip xs (map f ys) = map (id *** f) (zip xs ys)|.
:::
:::{.exans}
顯然 |select [] = []|。考慮 |xs := x:xs| 的情況：
```{.haskell .invisible}
selectDer1 x xs =
```
```haskell
    select (x:xs)
 ===   {- |select| 與 |delete| 之定義 -}
    zip (x:xs) (xs : map (x:) (delete xs))
 ===   {- |zip| 之定義 -}
    (x, xs) : zip xs (map (x:) (delete xs))
 ===   {- |zip xs (map f ys) = map (id *** f) (zip xs ys)| -}
    (x, xs) : map (id *** (x:)) (zip xs (delete xs))
 ===   {- |select| 之定義 -}
    (x, xs) : map (id *** (x:)) (select xs) {-"~~."-}
```
{.nobreak}因此，
```spec
select []      = []
select (x:xs)  = (x, xs) : map (id *** (x:)) (select xs) {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:delete-take-drop}
函數 |delete| 有另一個可能定義：
```spec
delete xs = map (del xs) [0..length xs-1]
   where del xs i = take i xs ++ drop (1+i) xs {-"~~,"-}
```
{.nobreak}（此處我們利用了當 |n| 為負數時，|[0..n]| 化簡成 |[]| 的特性。）
請用此定義推導出 |delete| 的歸納定義。**提示**：你可能用得上下述性質：
```{.equation #eq:gen-split}
  |[0..n] = 0 : map (1+) [0..n-1]|\mbox{,~~ if |n >= 0|,}
```
:::
:::{.exans}
以下只列出歸納狀況：
```{.haskell .invisible}
deleteDer1 x xs =
```
```haskell
    delete (x:xs)
 ===   {- |delete| 之定義 -}
    map (del (x:xs)) [0..length (x:xs) -1]
 ===   {- |length| 之定義，簡單運算 -}
    map (del (x:xs)) [0..length xs]
 ===   {- 由於 |length xs >= 0|, 使用 \eqref{eq:gen-split} -}
   map (del (x:xs)) (0 : map (1+) [0..length xs-1])
 ===   {- |map| 之定義 -}
   del (x:xs) 0 : map (del (x:xs)) (map (1+) [0..length xs-1])
 ===   {- |map| 融合 -}
   del (x:xs) 0 : map (del (x:xs) . (1+)) [0..length xs-1] {-"~~."-}
```
{.nobreak}在此暫停一下，觀察 |del (x:xs)|. 顯然, |del (x:xs) 0 = xs|. 至於 |del (x:xs) . (1+)|，我們演算看看:
```{.haskell .invisible}
del xs i = take i xs ++ drop (1+i) xs

delSucDer x xs i =
```
```haskell
    (del (x:xs) . (1+)) i
 ===    {- |(.)| 與 |del| 之定義 -}
    take (1+ i) (x:xs) ++ drop (1+ (1+ i)) (x:xs)
 ===    {- |take| 與 |drop| 之定義 -}
    x : take i xs ++ drop (1+ i) xs
 ===    {- |del| 之定義 -}
    x : del xs i
 ===    {- |(.)| 之定義 -}
    ((x:) . del xs) i {-"~~."-}
```
{.nobreak}繼續之前的演算：
```{.haskell .invisible}
deleteDer2 x xs =
```
```haskell
    del (x:xs) 0 : map (del (x:xs) . (1+)) [0 .. length xs - 1]
 ===   {- 前述之演算 -}
    xs : map ((x:) . del xs) [0 .. length xs - 1]
 ===   {- |map| 融合 -}
    xs : map (x:) (map (del xs) [0 .. length xs - 1])
 ===   {- |delete| 之定義 -}
    xs : map (x:) (delete xs) {-"~~."-}
```
{.nobreak}由此，我們導出了正文中 |delete| 的歸納定義.
:::
:::


## 關於執行效率 {#sec:efficiency-basics}

有點意外地，本書直到現在才較正式地談執行效率。
在本書中，我們假設數字四則運算、邏輯運算元等等都可在常數時間內完成。
資料結構方面，使用資料建構元或對其做樣式配對都只需要常數時間。
例如，將 |x| 與 |y| 做成 |(x,y)| 是常數時間內可完成的動作；一個型別是序對的值如果已經是弱首範式，將其配對成 |(x,y)| 以取出其中的 |x| 和 |y| 也只需要常數時間。
如果有資料結構定義 |data T = A || B|, 給一個已經是弱首範式的 |x :: T|, 只需常數時間便可判斷它究竟是 |A| 還是 |B|.

回顧 |List| 的定義：
```spec
data List a = [] | a : List a {-"~~."-}
```
{.nobreak}我們可看出這是一個偏一邊的表示法。
對於串列的左邊的操作都可以在常數時間內完成。
因此，我們可在常數時間內判斷一個串列 |xs| 究竟是 |[]| 還是可分解成頭和尾；
產生 |[]| 只需要常數時間；在 |xs| 的左邊添加一個元素，傳回 |x:xs|，也是常數時間內可完成的動作。
但如果我們要拿出某串列最右邊的元素，或著在串列的右邊加東西呢？回顧 |(++)| 的定義：
```spec
(++) :: List a -> List a -> List a
[]      ++ ys  = ys
(x:xs)  ++ ys  = x : (xs ++ ys) {-"~~."-}
```
{.nobreak}若我們試著看看 |[1,2,3] ++ [4,5]| 是怎麼被算出來的
```spec
   (1 : 2 : 3 : []) ++ (4 : 5 : [])
=  1 : ((2 : 3 : []) ++ (4 : 5 : []))
=  1 : 2 : ((3 : []) ++ (4 : 5 : []))
=  1 : 2 : 3 : ([] ++ (4 : 5 : []))
=  1 : 2 : 3 : 4 : 5 : [] {-"~~,"-}
```
{.nobreak}可發現 |(++)| 需把第一個參數從頭到尾走過一遍。
因此，若第一個參數的長度是 |n|，|(++)| 是一個時間複雜度為 $O(n)$ 的函數。
函數 |last| 的情況也類似。

:::{.exlist}
:::{.exer #ex:last-bigO}
回顧 |last| 的定義，試著展開 |last [1,2,3,4]| 並確認 |last xs| 需要的時間是否為 $O(|length xs|)$。
:::
:::

諸如 |sum|, |length|, |maximum| 之類的函數將串列從頭到尾走過一次。
當輸入串列長度為 |n|, 它們均需時 $O(n)$。如果函數 |f| 需時 $O(t)$，|map f| 需時 $O(t\times n)$.
函數 |filter p|, |takeWhile p| 等等在最壞情況下需將串列走完，因此它們也是需要線性時間的函數。
函數 |zip| 需要的時間與兩個串列中較短者成正比。

在習題 \@ref{ex:reverse} 中，我們曾請讀者定義一個函數 |reverse :: List a -> List a|，將輸入的串列反轉，例如 |reverse [1,2,3,4,5] = [5,4,3,2,1]|. 一個可能的答案如下：
```spec
reverse []      = []
reverse (x:xs)  = reverse xs ++ [x] {-"~~."-}
```
{.nobreak}這個程式的效率如何呢？我們看看 |reverse [1,2,3,4]| 如何被歸約：
```spec
   reverse [1,2,3,4]
=  reverse [2,3,4] ++ [1]
=  (reverse [3,4] ++ [2]) ++ [1]
=  ((reverse [4] ++ [3]) ++ [2]) ++ [1]
=  (((reverse [] ++ [4]) ++ [3]) ++ [2]) ++ [1]
=  ((([] ++ [4]) ++ [3]) ++ [2]) ++ [1] {-"~~."-}
```
{.nobreak}為了把 |[1]| 接在左邊，|(++ [1])| 需要走過一個長度為 |3| 的串列。
而在那之前，|(++ [2])| 需要走過一個長度為 |2| 的串列。
推廣說來，要反轉一個長度為 |n| 的串列，|(++)| 會被使用 $O(n)$ 次。每個 |(++)| 左邊的串列長度也是 $O(n)$，因此 |reverse| 是一個需時 $O(n^2)$ 的演算法！
「反轉串列」這個看來很基本的操作竟需要 $O(n^2)$ 的時間，似乎令人難以接受。
是否有更快的做法呢？我們將在第 \@ref{sec:accumulating-param} 節討論到。

:::{.exlist}
:::{.exer #ex:ETree-tips}
回顧第\@ref{sec:user-defined-data}與\@ref{sec:other-inductive-datatypes}節中提及的
外標籤二元樹：
```spec
data ETree a  = Tip a | Bin (ETree a) (ETree a) {-"~~."-}
```
{.nobreak}以下函數傳回樹中所有的標籤：
```haskell
tips :: ETree a -> List a
tips (Tip x)    = [x]
tips (Bin t u)  = tips t ++ tips u {-"~~."-}
```
{.nobreak}函數 |tips| 最壞情況的時間複雜度為何？請做出一個含有 |n| 個標籤的樹 |t|，使得 |tips t| 僅需要 $O(n)$ 的時間算完；也請做出一個含有 |n| 個標籤的樹 |u|，使得 |tips u| 需要 $O(n^2)$ 的時間。
:::
:::{.exans}
令 |t| 為一個向右傾斜的樹：
```spec
t = Bin (Tip 1) (Bin (Tip 2) .. (Bin (Tip (n-1)) (Tip n))) {-"~~,"-}
```
{.nobreak}|tip t| 展開成為 |[1] ++ ([2] .. ([n-1] ++ [n]))|, 可在 $O(n)$ 時間內歸約成範式。
這是最好的情況。
令 |u| 為一個向左傾斜的樹：
```spec
u =  Bin (Bin (... (Bin (Bin (Tip 1) (Tip 2)) (Tip 3)))...
       (Tip (n-1))) (Tip n) {-"~~,"-}
```
{.nobreak}|tip u| 展開成為 |((..(([1] ++ [2])++[3])..) .. ++ [n-1]) ++ [n]|, 需要 $O(n^2)$ 的時間，也是 |tips| 最壞情況的時間複雜度.
:::
:::

## 用展開-收回轉換增進效率 {#sec:fold-unfold-transform-efficiency}

在前面的例子中，我們手動推導出的 |sumsq| 只比原來的版本快了一點點，並沒有複雜度上的改進。
本節我們來看一些使用程式推導改進複雜度的例子。

### 計算多項式 -- Horner 法則 {#sec:poly-horner}

給定整數串列 $\Varid{as} = [a_0, a_1, a_2 \ldots a_n]$ 以及 |x :: Int|, 我們想計算如下的多項式：
```equation
    a_0 + a_1 x + a_2 x^2 + ... + a_n x^n \mbox{~~.}
```
這問題的規格能清楚寫成：
```haskell
poly x as = sum (zipWith (*) as (iterate (* x) 1)) {-"~~,"-}
```
{.nobreak}其中 |iterate (* x) 1| 產生無限串列 $[1, x, x^2, x^3 ...]$, |zipWith| 計算 $[a_0, a_1 x, \ldots a_n x^n]$, |sum| 計算總和。

讀者應已對 |sum| 和 |zipWith| 很熟悉了。函數 |iterate| 在第 \@ref{sec:list-generation} 節中使用過，|iterate f x| 會展開為無限長的串列 |[x, f x, f (f x)...]|，每個元素分別是把 |f| 使用|0|次、|1|次、|2|次... 的結果。
函數 |iterate| 可定義為
```spec
iterate :: (a -> a) -> a -> List a
iterate f x = x : map f (iterate f x) {-"~~."-}
```
{.nobreak}我們可將之理解成：|iterate f x| 的第一個元素是 |x|；剩下的元素呢？是把 |iterate f x| 本身拿來，對每個元素多做一次 |f|!

讀到此的讀者可能有些疑問：這是一個合法的歸納定義嗎？以及，我們原已說定不談無限的資料結構，何以在此卻出現了呢？

上述 |iterate| 的定義方式確實不是歸納，而是「餘歸納」(coinduction)的一個例子。\index{coinduction 餘歸納}
第\@ref{sec:induction-set-theory}節中曾提及，餘歸納與歸納互為對偶，以餘歸納定義出的資料結構稱作「餘資料」，可以是能無限地展開的。\index{codata 餘資料}
「餘串列」和歸納定義的串列應該視為不同的型別，但它們可共存於同一個程式中，只要我們確定不在餘資料上做歸納定義或證明。

為培養一些對 |iterate| 的直覺，我們試著展開它：
```spec
  iterate f x
=   {- |iterate| 之定義 -}
  x : map f (iterate f x)
=   {- |map| 之定義 -}
  x : map f (x : map f (iterate f x))
=   {- |map| 融合 -}
  x : f x : map (f . f) (iterate f x)
=   {- |iterate| 與 |map| 之定義 -}
  x : f x : f (f x) : map (f . f) (map f (iterate f x))
=   {- |map| 融合 -}
  x : f x : f (f x) : map (f . f . f) (iterate f x)
```
{.nobreak}可發現越展開，式子中便累積越多個 |map f|.

在 |poly| 之中，|iterate| 雖產生無限長的餘資料，但立刻被 |zipWith| 截短了。
^[此處我們假設 |as| 為有限長的串列，並把 |zipWith| 視為在其第一個參數之上的歸納定義。]
若我們試著展開 |poly x [a,b,c,d]|, 會得到：
```texonly
%{
%format (quad f) = f"^4"
```
```spec
   poly x [a,b,c,d]
=  sum (zipWith (*) [a,b,c,d] (iterate (* x) 1))
=    {- 展開 |iterate|, 將「|f|自我組合四次」記為 |quad f| -}
   sum (zipWith (*) [a,b,c,d]
     (1 : (1*x) : (1*x*x) : (1*x*x*x) : map (quad (*x)) (iterate (*x) 1)))
=  a {-"\,"-}+{-"\,"-} b *x {-"\,"-}+{-"\,"-} c * x * x {-"\,"-}+{-"\,"-} d * x * x * x {-"~~."-}
```
```texonly
%}
```
可看到式子越長，便累積越多個 |(*x)|。當 |as| 長度為 |n|, 需要的乘法數目為 $O(n^2)$.
我們有可能降低做乘法的次數嗎？

我們試著找出 |poly| 在 |as| 上的歸納定義。
當 |as := []| 時，|poly x []| 可歸約為 |0|.
考慮 |as := a:as| 的情況，和做證明時一樣，我們先將 |poly x (a:as)| 展開，然後試著整理出 |sum (zipWith (*) as (iterate (* x) 1)|，以便收回成為 |poly x as|。
計算中的每一步都以此為目的，試著將 |sum| 與 |zipWith| 移動至 |iterate| 旁邊:
```{.haskell .invisible}
polyDer1 x a as =
```
```{.haskell #ex:polyDer1}
      poly x (a : as)
 ===   {- |poly| 的定義 -}
      sum (zipWith (*) (a:as) (iterate (* x) 1))
 ===   {- |iterate| 的定義 -}
      sum (zipWith (*) (a:as) (1 : map (* x) (iterate (* x) 1)))
 ===   {- |zipWith| 與 |sum| 的定義 -}
      a + sum (zipWith (*) as (map (* x) (iterate (* x) 1)))
 ===   {- |zipWith (*) as . map (* x) = map (* x) . zipWith (*) as|，見習題 -}
      a + sum (map (* x) (zipWith (*) as (iterate (* x) 1)))
 ===   {- |sum . map (* x) = (* x) . sum| -}
      a + (sum (zipWith (*) as (iterate (* x) 1))) * x
 ===   {- |poly| 的定義 -}
      a + (poly x as) * x {-"~~."-}
```
{.nobreak}第 |4| 步中關於 |zipWith| 與 |map| 的性質幫助我們將 |map (*x)| 往外提、將 |zipWith| 往裡推。事實上，該性質不限於乘法，而可適用於任何滿足結合律的運算子 |otimes|。我們可非正式地理解如下：
```spec
   zipWith otimes [a,b,c] (map (`otimes` x) [d,e,f])
=  [a `otimes` (d `otimes` x), b `otimes` (e `otimes` x), c `otimes` (f `otimes` x)]
=    {- 結合律: |m `otimes` (n `otimes` k) = (m `otimes` n) `otimes` k| -}
   [(a `otimes` d) `otimes` x, (b `otimes` e) `otimes` x, (c `otimes` f) `otimes` x]
=  map (`otimes` x) (zipWith otimes [a,b,c] [d,e,f]) {-"~~."-}
```
{.nobreak}第 |5| 步之中的 |sum . map (* x) = (* x) . sum| 在習題\@ref{ex:sum-map-times}中證明過，需要乘法與加法的分配律。
在本推導中，它的功能是將 |sum| 往右推。
它也是使 |poly| 可以加速的關鍵性質：共同的 |(*x)| 可以提出來 ---
左手邊可能做了的許多次 |(*x)| 其實只需做一次。
追根究底，|poly| 之所以能算得更快，都歸功於乘法與加法的分配律。
經過上述計算，我們可得：
```spec
poly x []        = 0
poly x (a : as)  = a + (poly as) * x {-"~~."-}
```
{.nobreak}在這個定義中，函數 |poly| 遞迴多少次，便做多少個乘法。
因此本演算法所需的乘法數目為 $O(n)$.

快速版本的函數 |poly| 相當於把 $a_0 + a_1 x + a_2 x^2 + ... + a_n x^n$ 轉換成
```equation
    a_0 + x \times (a_1 + x \times (a_2 + ... + (a_{n-1} + x \times a_n)))\mbox{~~.}
```
這條規則在 William George Horner 1819 年的一篇論文中出現並證明，因此通常被稱作 *Horner 法則*\index{Horner法則 Horner's rule}，
雖然 Horner 本人和許多歷史學家們都相信該規則可被追溯得更早。

```texonly
% % map f (iterate f x) = iterate f (f x)
% % zipWith (⊗) as . map (⊗X) = map (⊗X) . zipWith (⊗) as, 如果 ⊗ 滿足結合律
% % sum . map (×X) = (×X) . sum, a special case of foldr ⊕ e . map (⊗X) = (⊗X) . foldr ⊕ e, 如果 (a ⊕ b) ⊗ X = (a ⊗ X) ⊕ (b ⊗ X), 且 e ⊗ X = e.
%
```

:::{.exlist}
:::{.exer #ex:zipWith-otimes-map}
試證明：如果 |otimes| 滿足結合律，|zipWith otimes as . map (`otimes` x) = map (`otimes` x) . zipWith otimes as|。
:::
:::{.exans}
欲證明|zipWith otimes as (map (`otimes` x) bs) = map (`otimes` x) (zipWith otimes as bs)|, 在 |as| 上做歸納。
當 |as := []|, 等號兩邊都歸約成 |[]|.
考慮 |as := a:as| 的情況。若 |bs := []|, 等號兩邊仍均為 |[]|.
當 |bs := b:bs|:
```{.haskell .invisible}
zipWithOTimesMap :: (a -> a -> a) -> a -> [a] -> a -> a -> [a] -> [a]
zipWithOTimesMap otimes a as x b bs =
```
```haskell
      zipWith otimes (a:as) (map (`otimes` x) (b:bs))
 ===    {- |zipWith| 與 |map| 之定義 -}
      (a `otimes` (b `otimes` x)) : zipWith otimes as (map (`otimes` x) bs)
 ===    {- 歸納假設 -}
      (a `otimes` (b `otimes` x)) : map (`otimes` x) (zipWith otimes as bs)
 ===    {- |otimes| 滿足結合律 -}
      ((a `otimes` b) `otimes` x) : map (`otimes` x) (zipWith otimes as bs)
 ===    {- |zipWith| 與 |map| 之定義 -}
      map (`otimes` x) (zipWith otimes (a:as) (b:bs)) {-"~~."-}
```
:::
:::

### 二進位表示法 {#sec:exp-binary-roll}

回顧第\@ref{sec:induction-on-Nat}節中的函數 |exp|。該函數計算乘冪 --- $|exp b n| = b^n$，其定義如下:
```spec
exp :: Nat -> Nat -> Nat
exp b Zero     = 1
exp b (Suc n)  = b *: exp b n {-"~~."-}
```
{.nobreak}以這個演算法計算 $b^n$ 時會需要 $O(n)$ 個乘法。是否有更快的做法呢？
```texonly
%{
%format tt = "\mymathbb{1}"
%format ff = "\mymathbb{0}"
```
```{.haskell .invisible}
tt = True
ff = False

exp2 :: Int -> List Bool -> Int
exp2 b = exp b . decimal
```

我們先定義函數 |binary :: Nat -> List Bool|，可將一個自然數轉換成*反轉*的二進位表示法（即最低有效位在左邊，最高有效位在右邊）。以下我們將 |False| 簡寫為 |ff|, |True| 簡寫為 |tt|：
```haskell
binary 0  = []
binary n  | even n  = ff : binary (n `div` 2)
          | odd n   = tt : binary (n `div` 2) {-"~~."-}
```
{.nobreak}例如，|map binary [1,2,3,4] = [[tt], [ff,tt], [tt,tt], [ff,ff,tt]]|.
函數 |binary| 在每次遞迴呼叫時將參數減半，因此 |binary n| 只需要 $O(\log n)$ 的時間。
我們讓 |binary| 傳回反轉的二進位數是為了方便定義 |decimal :: List Bool -> Nat| --- |binary| 的反函數，將 |binary| 的結果轉回成原有的數字：
```haskell
decimal []      = 0
decimal (c:cs)  = if c then 1 + 2 * decimal cs else 2 * decimal cs {-"~~."-}
```
{.nobreak}我們可證明 |decimal . binary = id|.

回到 |exp|, 試計算如下
```spec
   exp b
=    {- |id| 為 |(.)| 的單位元 -}
   exp b . id
=    {- |decimal . binary = id| -}
   exp b . decimal . binary {-"~~."-}
```
{.nobreak}由於 |binary n| 只需 $O(\log n)$ 的時間，如果我們能把 |exp b . decimal| 的計算時間也縮減到 $O(\log n)$, 我們就有個只需對數時間的演算法了！

令 |roll b = exp b . decimal|。顯然 |roll b [] = 1|. 考慮輸入為 |c:cs| 的情況，在以下的推導中，我們假設 $|exp b n| = b^n$ 擁有乘冪該有的各種算術性質：
```{.haskell .invisible}
roll b = exp b . decimal

rollDer :: Int -> Bool -> [Bool] -> Int
rollDer b c cs =
```
```haskell
    roll b (c:cs)
 ===    {- |exp2| 與 |decimal| 之定義  -}
    exp b (if c then 1 + 2 * decimal cs else 2 * decimal cs)
 ===    {- 函數分配進 |if| -}
    if c then exp b (1 + 2 * decimal cs) else exp b (2 * decimal cs)
 ===    {- 算術：$b^{i + 2 \times x} = b^i \times {(b^x)}^2 $ -}
    if c then b * square (exp b (decimal cs)) else square (exp b (decimal cs))
 ===    {- |roll| 之定義  -}
    if c then b * square (exp2 b cs) else square (roll b cs){-"~~."-}
```
{.nobreak}因此，我們推導出了在 $O(\log n)$ 時間內計算 $b^n$ 的程式如下：
```spec
exp b = roll b . binary

roll b []      = 1
roll b (c:cs)  = if c then b * square (exp2 b cs) else square (exp2 b cs){-"~~."-}
```

:::{.exlist}
:::{.exer #binary-termination}
如何得知 |binary| 會終止？它的定義用的是什麼歸納方式？
:::
:::{.exer #ex:decimal-binary-id}
證明 |decimal . binary = id|.
:::
:::{.exer #ex:exp-roll-binary}
展開 |exp b = roll b . binary| 以導出一個不產生中間串列的 |exp| 定義。
這個定義用的是什麼歸納方式呢？
:::
:::{.exans .compact}
```haskell
exp b 0 = 1
exp b n  | even n  = square (exp b (n `div` 2))
         | odd n   = b * square (exp b (n `div` 2)) {-"~~."-}
```
{.nobreak}由於遞迴呼叫中的 |n| 總是變小，本定義可視為 |n| 之上的良基歸納。
:::
:::


```texonly

%} % for tt and ff
```

### 小結與提醒 {#sec:wrap-reminder}

如果回顧本節發生了什麼，該說：我們為 |poly| 和 |roll . decimal| 找出了歸納定義。
它們的效率因此提升了，但這只能說是*湊巧*：兩個演算中，都有些代數性質可運用，使得推導出的歸納定義在每一步需要做的工作不多，剛好是有效率的。

一般說來，歸納定義和效率提升不見得能畫上等號。導出了某函數的歸納定義後，仍需針對它做分析，才能知道這個推導是否值得。
有些情況下，推導出的程式有較好的時間複雜度，這樣的程式*通常*能表現得比原來的程式好。
有些情況下，找出歸納定義能消除中間串列，或著減少走訪資料結構的次數。
這時，導出的程式仍有同樣的時間複雜度，但*可能*有較小的常數。
此時需注意：本章談的僅是時間複雜度，而且只考慮一些特定運算元被使用的次數。
實際上的執行效率受到許多因素的影響，例如：不同運算元花費不同的時間；
空間的使用量也影響效率（例如，使用大量記憶體的程式可能需要較多次垃圾收集）；
某些演算法適合快取，等等。
我們在之後的章節中將看到一些歸納定義程式走訪資料結構的次數雖較少，但反而執行得慢的例子。

:::{.exlist}
:::{.exer #sublist-choose}
回顧第 \@ref{sec:fan-perm} 節的 |sublists|:
```spec
sublists :: List a -> List (List a)
sublists []      = [[]]
sublists (x:xs)  = sublists xs ++ map (x:) (sublists xs) {-"~~."-}
```
{.nobreak}定義
```spec
choose :: Nat -> List a -> List (List a)
choose k = filter ((k ==) . length) . sublists {-"~~,"-}
```
{.nobreak}使得 |choose k xs| 傳回 |xs| 的子串列中長度為 |k| 者，例如 |choose 3 "abcde" =| |["cde","bde","bce","bcd","ade","ace",| |"acd",| |"abe",| |"abd","abc"]|.
使用展開-收回轉換導出 |choose| 的歸納定義。
**提示**: 依照 |choose k xs| 的定義，我們會在 |xs| 上做歸納。但此例之中，先對 |k| 做歸納，再對 |xs| 做歸納，得到的程式會比較精簡。
:::
:::{.exans}
先對 |k| 做歸納，再對 |xs| 做歸納。我們只列出最複雜的情況：

{.noindent}**情況** |k := Suc k|, |xs := x:xs|.
```{.haskell .invisible}
length' = Induction.length
chooseDerInd k x xs =
```
```haskell
     choose (Suc k) (x:xs)
 ===   {- |choose| 之定義 -}
     filter ((Suc k ==) . length') (sublists (x:xs))
 ===   {- |sublists| 之定義 -}
     filter ((Suc k ==) . length') (sublists xs ++ map (x:) (sublists xs))
 ===   {- |filter| 分配入 |(++)| -}
     filter ((Suc k ==) . length') (sublists xs) ++
     filter ((Suc k ==) . length') (map (x:) (sublists xs))
 ===   {- |choose| 之定義 -}
     choose (Suc k) xs ++
     filter ((Suc k ==) . length') (map (x:) (sublists xs))
 ===   {- 定理 \ref{thm:filter-map} -}
     choose (Suc k) xs ++
     map (x:) (filter ((Suc k ==) . length' . (x:)) (sublists xs))
 ===  {- |(Suc k ==) . length' . (x:) = (k ==) . length'| -}
     choose (Suc k) xs ++
     map (x:) (filter ((k ==) . length') (sublists xs))
 ===  {- |choose| 之定義 -}
     choose (Suc k) xs ++
     map (x:) (choose k xs) {-"~~."-}
```

我們得到：
```haskell
choose :: Nat -> List a -> List (List a)
choose Zero     xs      =  [[]]
choose (Suc k)  []      =  []
choose (Suc k)  (x:xs)  =  choose (Suc k) xs ++
                           map (x:) (choose k xs) {-"~~."-}
```
{.nobreak}確實是一般組合數學教材中會給的 $C^n_k$ 定義。
:::
:::

## 變數換常數 {#sec:var-cons}

接下來的幾節中，我們將介紹幾種常見的程式推導技巧。
\todo{generalize}

本節先以一個簡單但時常用上的技巧作為開頭。
回顧在例 \@ref{ex:positions} 中提及的函數 |positions|:
```spec
positions z = map fst . filter ((==z) . snd) . zip [Zero..] {-"~~."-}
```
{.nobreak}|positions z xs| 傳回 |z| 在 |xs| 中出現的所有位置。
上述的定義方式會產生許多中間串列。
我們能用第 \@ref{sec:fold-unfold-transform} 節中的方式，利用展開-收回轉換為 |positions| 推導出一個歸納定義，並藉此將中間串列消除嗎？

我們針對 |positions z| 的輸入做分析，
在歸納狀況中，先將 |positions z (x:xs)| 展開，希望最後能收回 |positions z xs|.
由於讀者對相關計算應已熟悉，以下的演算以較快的步調進行：
```{.haskell .invisible}
positionsDer1 ::Eq a => a -> a -> List a -> List Nat
positionsDer1 z x xs =
```
```haskell
      positions z (x:xs)
 ===  map fst . filter ((==z) . snd) . zip [Zero .. ] $ (x:xs)
 ===    {- |zip| 之定義， |[0..] = 0 : [1..]| -}
      map fst . filter ((==z) . snd) $ (Zero,x) : zip [1..] (x:xs)
 ===    {- |map| 與 |filter| 之定義 -}
      if x==z then Zero : map fst (filter ((==z) . snd) (zip [1..] (x:xs)))
         else map fst (filter ((==z) . snd) (zip [1..] (x:xs))) {-"~~."-}
```
{.nobreak}結果我們卡在這兒了：最後的式子中，|zip| 的參數是 |[1..]|, 但 |positions| 的定義要求這個參數得是 |[Zero ..]|. 我們無法將式子收回得到 |positions z xs|.

看來，問題是 |positions| 的定義把 |Zero| 給寫死了。如果我們索性把該位置變成一個變數呢？
我們定義：
```haskell
posFrom z i = map fst . filter ((z==) . snd) . zip [i..]
```
{.nobreak}函數 |positions| 是 |posFrom| 的特例：|positions z = posFrom z 0|.
而 |posFrom| 的歸納定義可用展開-收回轉換找出：
```{.haskell .invisible}
posFromDer1 :: Eq a => a -> Nat -> a -> List a -> List Nat
posFromDer1 z i x xs =
```
```haskell
      posFrom z i (x:xs)
 ===  map fst . filter ((==z) . snd) . zip [i..] $ (x:xs)
 ===    {- |zip| 之定義， |[i..] = i : [Suc i..]| -}
      map fst . filter ((==z) . snd) $ (i,x) : zip [Suc i..] (x:xs)
 ===    {- |map| 與 |filter| 之定義 -}
      if x==z then i : map fst (filter ((==z) . snd) (zip [Suc i..] (x:xs)))
         else map fst (filter ((==z) . snd) (zip [Suc i..] (x:xs)))
 ===    {- |posFrom| 之定義 -}
      if x==z then i : posFrom z (Suc i) xs
         else posFrom z (Suc i) xs {-"~~."-}
```
{.nobreak}由此我們可得：
```spec
posFrom z i []      =  []
posFrom z i (x:xs)  =  if x==z then i : posFrom z (1+i) xs
                         else posFrom z (1+i) xs {-"~~."-}
```

由於將一個常數換成變數，|posFrom| 比 |positions| 多了些彈性，因此較容易收回。
這個技巧在許多場合用得上，往往是許多程式推導的第一步。
但我並不建議大家看到任一個定義，便一股腦地把所有常數都換成變數。
如同第\@ref{sec:using-hints-from-symbols}節中提及的原則，該把哪些常數換掉仍應由計算中發現，只用在必要之處。

:::{.exlist}
:::{.exer #ex:index-positioning}
函數 |index| 為串列中的每個元素標上位置。
```haskell
index :: List a -> List (Nat :* a)
index = zip [Zero .. ] {-"~~."-}
```
{.nobreak}請試著為 |index| 導出一個歸納定義。如果不成功，找出一個更通用的輔助函數，並導出其歸納定義。
:::
:::{.exans}
試著展開-收回 |index (x:xs)|：
```spec
     index (x:xs)
 === zip [Zero .. ] (x:xs)
 ===  {- |[Zero ..] = Zero: [1 ..]|, |zip| 之定義 -}
     (Zero,x) : zip [1..] xs {-"~~."-}
```
{.nobreak}我們又發現 zip [1..] 無法收回成 index xs.
因此，我們定義：
```haskell
indexFrom :: Nat -> List a -> List (Nat :* a)
indexFrom i = zip [i..] {-"~~."-}
```
{.nobreak}試著推導 |indexFrom| 的歸納定義如下：
```spec
     indexFrom i (x:xs)
 === zip [i .. ] (x:xs)
 ===  {- |[i ..] = i: [Suc i ..]|, |zip| 之定義 -}
     (i,x) : zip [Suc i..] xs
 === (i,x) : indexFrom (Suc i) xs {-"~~."-}
```
{.nobreak}因此我們已得到：
```spec
indexFrom i []      = []
indexFrom i (x:xs)  = i,x) : indexFrom (Suc i) xs {-"~~."-}
```
:::
:::

## 組對 {#sec:tupling}

接下來我們介紹另一個重要的技巧：「組對(tupling)」。

### 陡串列 {#sec:steep}
給定一個整數串列。當我們說它很「陡」，意思是它由左到右下降得極快，快到每一個元素都大於其右邊所有元素的和。形式化的定義如下：
```haskell
steep :: List Int -> Bool
steep []      = True
steep (x:xs)  = x > sum xs && steep xs {-"~~."-}
```
{.nobreak}如果當作一個程式，當輸入串列長度為 |n|, 由於反覆呼叫 |sum|, 上述的程式需要 $O(n^2)$ 的時間。
但每次算出的 |sum xs| 和 |x| 比較後便立刻被丟棄，似乎很浪費。我們能否把 |sum| 的結果存下來呢？
下述函數 |steepsum| 把 |steep| 與 |sum| 都算出來，放在一個序對中：
```spec
steepsum :: List Int -> (Bool :* Int)
steepsum xs = (steep xs, sum xs) {-"~~."-}
```
{.nobreak}我們看看 |steepsum| 能否算得快一點？

根據定義，|steepsum [] = (True, 0)|. 我們看看 |xs = x:xs| 的例子：
```{.haskell .invisible}
steepsumDer1 :: Int -> List Int -> (Bool :* Int)
steepsumDer1 x xs =
```
```haskell
      steepsum (x:xs)
 ===    {- |steepsum| 之定義 -}
      (steep (x:xs), sum (x:xs))
 ===    {- |steep| 與 |sum| 之定義 -}
      (x > sum xs && steep xs, x + sum xs)
 ===    {- 將子算式提取至 |let| 中 -}
      let (b, s) = (steep xs, sum xs)
      in (x > s && b, x + s)
 ===    {- |steepsum| 之定義 -}
      let (b, s) = steepsum xs
      in (x > s && b, x + s) {-"~~."-}
```
{.nobreak}我們已推導出：
```haskell
steepsum []      =  (True, 0)
steepsum (x:xs)  =  let (b, s) = steepsum xs
                    in (x > s && b, x + s) {-"~~."-}
```
{.nobreak}這是一個只用 $O(n)$ 時間的程式。
有了 |steepsum|，我們可重新定義 |steep| 為 |steep = fst . steepsum|。

讓一個函數*多傳回一些值*的動作稱作*組對*(*tupling*) --- 因為多傳回的值被放在一個序對中。\index{tupling 組對}
^[在一些函數語言中，``pair'' 指含兩個成員的序對，``tuple'' 則不限定為兩個成員。Tuple 也可當作動詞，指做出一個 tuple. 本書將動詞的 tuple 譯為「組對」-- 組出一個對。有些語言中 pair 與 tuple 有更根本的差異，但本書中不做區分。]
我們常用此技巧來存下可重複使用的中間值，並減少走訪資料結構的次數。

最後一提：若使用第\@ref{sec:pairs}節，\@pageref{par:split-product}頁介紹的「分裂」運算元：
\index{pair 序對!split 分裂}
```spec
fork :: (a -> b) -> (a -> c) -> a -> (b :* c)
(fork f g) x = (f x, g x) {-"~~."-}
```
{.nobreak}函數 |steepsum| 的定義可較簡潔地寫成：
```spec
steepsum = fork steep sum {-"~~."-}
```
{.nobreak}本書將在適當時採用這種寫法。

{title="責任越大，能力越強？"}
某個意義上，函數 |steepsum| 做的事比 |steep| 多：
後者只判斷輸入是否為陡串列，前者不只如此，還多附送了串列的和。
然而，傳回較多東西、似乎做了更多事的程式，反倒可以執行得比較快。
竟出現「責任越大，能力越強」這種違反直覺的現象，這是怎麼回事呢？
^[「能力越強，責任越大 (with great power comes great responsibility)」是 2002 年版《蜘蛛人》電影的名句。根據考證[@OToole:15:Great], 法國國民公會1793年的政令中即出現過類似的想法，包括邱吉爾和羅斯福等人也都說過類似話語的不同版本。]

其實，在歸納定義與歸納證明中，這都是常見的。
有些比較通用的程式反倒比較容易定義；有些定理本身不好證明，為了證明它，我們把它變得更廣泛、更強些，反倒好證了。
箇中原因說穿了便不難理解，
函數 |steepsum| 便是一個容易明白的好例子：一個函數若傳回較多資訊，在遞迴呼叫它時，我們便有更多資訊可直接取用。
同樣地，一個定理若保證更強的性質，表示在使用歸納假設的步驟中，我們有了更強的性質可用。

如果我們把一個函數或待證的定理擴充得太強，確實也有可能使它們強到寫不出來、證不出來。
做歸納定義或證明的重要技巧之一，便是找到這麼一個平衡點：將一個待定義或證明的物件擴充到足以提供歸納步驟需要的所有資訊，又不至於強到無法寫出、證出。

在這一節以及下一節中，我們都會看到許多如此的例子。

### 以串列標記樹狀結構 {#sec:repl-tree}

我們再舉一個組對的好例子。回顧第 \@ref{sec:user-defined-data}與\@ref{sec:other-inductive-datatypes}節中提及的外標籤二元樹：
```spec
data ETree a  = Tip a | Bin (ETree a) (ETree a) {-"~~."-}
```
{.nobreak}下述函數 |size :: ETree a -> Int| 計算一棵樹中標籤的數目（對 |ETree| 而言是 |Tip| 出現的次數）； |repl t xs| 則將 |t| 原有的標籤丟棄，改用串列 |xs| 由右至左依序重新為 |t| 上標籤。
觀察：在遞迴呼叫中，我們用 |take| 和 |drop| 將串列 |xs| 截成適當的長度：
```haskell
size (Tip _)    = 1
size (Bin t u)  = size t + size u {-"~~,"-}

repl :: ETree a -> List b -> ETree b
repl (Tip _)    xs = Tip (head xs)
repl (Bin t u)  xs = Bin (repl t (take n xs)) (repl u (drop n xs))
    where n = size t {-"~~."-}
```
{.nobreak}如果 |t| 是一個向左傾斜的二元樹，|repl t xs| 不僅會反覆計算 |size|，也會反覆地將 |take| 與 |drop| 用在 |xs| 上，使得上述的 |repl| 成為一個 $O(n^2)$ 的演算法。
利用組對的技巧，我們能讓 |repl| 的時間複雜度小一些嗎？

```texonly
%{
%format n1
%format n2
```
我們試著把 |repl| 作用在一個稍微左斜的樹，|(Bin (Bin t u) v)| 之上，看看有什麼能做的。
令 |t|, |u| 的 |size| 分別為 |n1| 與 |n2|.
如果我們希望導出一個線性時間的程式，其中一個提示是：我們希望在 |repl (Bin (Bin t u) v) xs| 中，*|xs| 的每個元素最多都只被 |take| 和 |drop| 各碰過一次*。
依此原則，以下的推導基嘗試做到兩點：首先，把連續的 |take| 消去；其次，若已做了 |take n1 xs|，就避免再出現 |take (n1 + n2) xs|，因為後者的存在會讓 |take| 重複處理 |xs| 中的元素。
我們會用到習題 \@ref{ex:take-take} -- \@ref{ex:drop-drop} 中提到的三個性質：
```equation
|take m (take (m+n) xs)| ~&=~ |take m xs|
\mbox{~~,}\\
|drop m (take (m +: n) xs)| ~&=~ |take n (drop m xs)|\mbox{~~,}\\
|drop (m +: n) xs| ~&=~ |drop n (drop m xs)| \mbox{~~.}
```
其中 |m|, |n| 均為自然數。試演算如下：
```{.haskell .invisible}
replTrial t u v xs =
```
```haskell
      repl (Bin (Bin t u) v) xs
 ===    {- |repl| 之定義，兩次 -}
      Bin  (Bin  (repl t (take n1 (take (n1+n2) xs)))
                 (repl u (drop n1 (take (n1+n2) xs))))
           (repl v (drop (n1+n2) xs))
 ===    {- 習題 \ref{ex:take-take} -- \ref{ex:drop-drop} -}
      Bin  (Bin  (repl t (take n1 xs))
                 (repl u (take n2 (drop n1 xs))))
           (repl v (drop n2 (drop n1 xs)))  {-"~~."-}
```
```{.haskell .invisible}
 where (n1, n2) = (size t, size u)
```
演算到此，與 |t| 有關的是 |repl t|, |take (size t)|, 與 |drop (size t)| 三項；
與 |u| 有關的是 |repl u|, |take (size u)|, 與 |drop (size u)| 三項。
如果我們把 |repl t|, |take (size t)|, 與 |drop (size t)| 取出，當作一個函數之內完成的動作：
```haskell
repTail :: ETree a -> List b -> (ETree b :* List b)
repTail s xs = (repl s (take n xs), drop n xs) {-"~~,"-}
  where n = size s {-"~~."-}
```
{.nobreak}那麼 |Bin (repl t (take n1 xs)) (repl u (take n2 (drop n1 xs)))| 似乎有可能收回成為這樣的式子：|xs| 先被丟給 |repTail t|，將 |t| 標記好，並得到剩下的串列 |drop n1 xs|。這個剩下的串列又可以丟給 |repTail u|, 兩者都只把 |xs| 走過一次。
我們試著導出 |repTail| 的歸納定義。
基底狀況 |s := Tip y| 比較容易，我們考慮 |s := Bin t u| 的情況，
並演算如下（令 |n1 = size t|，|n2 = size u|, 因此 |size (Bin t u)= n1 + n2|）：
```{.haskell .invisible}
repTailDer1 :: ETree a -> ETree a -> List b -> (ETree b, List b)
repTailDer1 t u xs =
```
```haskell
      repTail (Bin t u) xs
 ===   {- |repTail| 之定義 -}
      (repl (Bin t u) (take (n1 + n2) xs), drop (n1 + n2) xs)
 ===   {- |repl| 之定義，令 |n1 = size t| -}
      (Bin  (repl t (take n1 (take (n1 + n2) xs)))
            (repl u (drop n1 (take (n1 + n2) xs))), drop (n1 + n2) xs)
 ===   {- 習題 \ref{ex:take-take} -- \ref{ex:drop-drop} -}
      (Bin  (repl t (take n1 xs))
            (repl u (take n2 (drop n1 xs))), drop n2 (drop n1 xs))
 ===   {- 提出共同項 -}
      let  (t', xs')   = (repl t (take n1 xs),  drop n1 xs)
           (u', xs'')  = (repl u (take n2 xs'), drop n2 xs')
      in (Bin t' u', xs'')
 ===   {- |repTail| 之定義 -}
      let  (t', xs')   = repTail t xs
           (u', xs'')  = repTail u xs'
      in (Bin t' u', xs'') {-"~~."-}
```
```{.haskell .invisible}
  where n = size (Bin t u)
        (n1, n2) = (size t, size u)
```
```texonly
%} % format n1 and n2
```
因此我們得到：
```spec
repTail (Tip _)    xs =  (Tip (head xs), tail xs)
repTail (Bin t u)  xs =  let  (t', xs')   = repTail t xs
                              (u', xs'')  = repTail u xs'
                         in (Bin t' u', xs'') {-"~~."-}
```
{.nobreak}確實如同所預期的，串列 |xs| 被 |repTail t| 使用，得到標籤過的新樹 |t'|, 和剩下的串列 |xs'|. 後者再被 |repTail u| 用來給 |u| 上標籤。最後我們得傳回剩下的串列 |xs''|. 實際上把串列變短的動作發生在基底狀況 |repTail (Tip _)| 中。串列中的每個元素只會在每次遇見 |Tip| 時被取出一次，因此這是一個線性時間的演算法。

\todo{|repsort t = rep t (sort (leaves t []))|.}

@BurstallDarlington:77:Transformation

:::{.exlist}
:::{.exer #ex:ascendingTuple}
下述函數 |ascending :: List Int -> Bool| 判斷一個串列是否由左到右遞增：
```haskell
ascending :: List Int -> Bool
ascending []      = True
ascending (x:xs)  = x <= minimum xs && ascending xs {-"~~."-}
```
{.nobreak}當輸入串列長度為 |n|, 這個函數需要 $O(n^2)$ 個基本運算。請用組對的方式將之減少至 $O(n)$.
:::
:::{.exans}
考慮如下的定義：
```spec
ascMin :: List Int -> (Bool :* Int)
ascMin = fork ascending minimum {-"~~."-}
```
{.nobreak}如果 |ascMin| 有更快的實作，我們可定義 |ascending = fst . ascMin|.

當輸入為 |[]|, 我們有 |ascMin [] = (True, maxBound)|. 考慮當輸入為 |x:xs| 的情況：
```{.haskell .invisible}
ascMinDerInd :: Int -> List Int -> (Bool, Int)
ascMinDerInd x xs =
```
```haskell
      ascMin (x:xs)
 ===   {- |ascMin| 之定義 -}
      (ascending (x:xs), minimum (x:xs))
 ===   {- |ascending| 與 |minimum| 之定義 -}
      (x <= minimum xs && ascending xs, x `min` minimum xs)
 ===   {- 引入區域變數 -}
      let (b, y) = (ascending xs, minimum xs)
      in (x <= y && b, x `min` y)
 ===   {- |ascMin| 之定義 -}
      let (b, y) = ascMin xs
      in (x <= y && b, x `min` y) {-"~~."-}
```
{.nobreak}如此，我們已導出：
```haskell
ascMin :: List Int -> (Bool, Int)
ascMin []      = (True, maxBound)
ascMin (x:xs)  =  let (b, y) = ascMin xs
                  in (x <= y && b, x `min` y) {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:baobab-ITree}
回顧第 \@ref{sec:user-defined-data} 節中談到的 |ITree|:
```spec
data ITree a = Null | Node a (ITree a) (ITree a) {-"~~."-}
```
{.nobreak}*猴麵包樹(baobab)*，又稱猢猻木，是一種樹幹相當粗的樹。
^[猴麵包樹原產於馬達加斯加、非洲等地，也被寫進了《小王子》之中。]
如果一個 |ITree Int| 的*每個*標籤都大於其兩個子樹的標籤總和，我們便說它是一棵猴麵包樹。
以下的函數判定一棵樹是否為猴麵包樹（其中 |sumT :: ITree Int -> Int| 計算一個樹中所有標籤的總和）：
```haskell
baobab :: ITree Int -> Bool
baobab Null          =  True
baobab (Node x t u)  =  baobab t && baobab u &&
                          x > (sumT t + sumT u) {-"~~."-}
```
{.nobreak}因反覆呼叫 |sumT|, 當樹的大小為 |n| 時，|baobab| 的執行時間為 $O(n^2)$.
請使用組對的技巧，在 $O(n)$ 的時間內算出 |baobab|.
:::
:::{.exans}
考慮如下的定義：
```spec
baosum :: Tree Int -> (Bool, Int)
baosum = fork baobab sumT {-"~~."-}
```
{.nobreak}如果 |baosum| 有時間效率為 $O(n)$ 的定義，我們可重定義 |baobab = fst . baosum|.
當 |t := Null|, 我們有 |baosum Null = (True, 0)|.
考慮 |t := Node x t u|:
```{.haskell .invisible}
sumT :: ITree Int -> Int
sumT = error ""

baosumDerInd :: Int -> ITree Int -> ITree Int -> (Bool, Int)
baosumDerInd x t u =
```
```haskell
     baosum (Node x t u)
 ===    {- |baosum| 之定義 -}
     (baobab (Node x t u), sumT (Node x t u))
 ===    {- |baobab| 與 |sumT| 之定義 -}
     (  baobab t && baobab u && x > (sumT t + sumT u),
        x + sumT t + sumT u)
 ===    {- 引入區域變數 -}
     let  (b,y) = (baobab t, sumT t)
          (c,z) = (baobab u, sumT u)
     in (b && c && x > (y + z), x + y + z)
 ===    {- |baosum| 之定義 -}
     let  (b,y) = baosum t
          (c,z) = baosum u
     in (b && c && x > (y + z), x + y + z) {-"~~."-}
```
{.nobreak}如此，我們已經導出：
```haskell
baosum Null          = (True, 0)
baosum (Node x t u)  =
  let  (b,y) = baosum t
       (c,z) = baosum u
  in (b && c && x > (y + z), x + y + z) {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:deepest}
本題出自@HuIwasaki:97:Tupling。
函數 |depth| 定義一棵 |ETree| 的*深度*。
|Tip| 的深度為零，|Bin| 的深度則為兩子樹中較深者的深度加一：
```haskell
depth :: ETree a -> Nat
depth (Tip _)    = Zero
depth (Bin t u)  = Suc (depth t `max` depth u) {-"~~."-}
```
{.nobreak}下列函數 |deepest| 則傳回一棵樹中最深的標籤：
```haskell
deepest :: ETree a -> List a
deepest (Tip x)    = [x]
deepest (Bin t u)  | m <  n  = deepest u
                   | m == n  = deepest t ++ deepest u
                   | m >  n  = deepest t
    where (m,n) = (depth t, depth u) {-"~~."-}
```
{.nobreak}請用組對的技巧，避免重複計算 |depth|.
**注意**: 完成的程式中，|(++)| 仍可能需要 $O(n^2)$ 的時間。
我們將在習題\@ref{ex:deepestAux}處理這個問題。
:::
:::{.exans}
定義：
```spec
dd :: ETree a -> (List a, Nat)
dd = fork deepest depth {-"~~."-}
```
{.nobreak}顯然 |dd (Tip x) = ([x], 0)|.
以下我們考慮歸納情況時，用一個非標準的語法同時處理守衛算式的三個式子：
```spec
      dd (Bin t u)
 ===   {- |dd|, |deepest|, 與 |depth| 之定義 -}
      (  ( m <  n  -> deepest u
         | m == n  -> deepest t ++ deepest u
         | m >  n  -> deepest t), 1 + (m `max` n))
      where (m,n) = (depth t, depth u)
 ===   {- 取出 |deepest t| 與 |deepest u| -}
      (  ( m <  n  -> ys
         | m == n  -> xs ++ ys
         | m >  n  -> xs), 1 + (m `max` n))
      where ((xs,m),(ys,n)) = ((deepest t,depth t), (deepest u, depth u))
 ===   {- |dd| 之定義，函數分配進條件判斷 -}
      ( m <  n  -> (ys, 1 + n)
      | m == n  -> (xs ++ ys, 1 + n)
      | m >  n  -> (xs, 1 + m))
      where ((xs,m),(ys,n)) = (dd t, dd u) {-"~~."-}
```
{.nobreak}因此我們得到：
```haskell
dd (Tip x)    = ([x],0)
dd (Bin t u)  | m <  n  = (ys, 1 + n)
              | m == n  = (xs ++ ys, 1 + n)
              | m >  n  = (xs, 1 + m) {-"~~,"-}
  where ((xs,m),(ys,n)) = (dd t, dd u) {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:red-black-tree-balanced-linear-time}
第 \@ref{sec:induction-red-black-tree} 節中的函數 |balanced :: RBTree -> Bool| 檢查一棵紅黑樹是否平衡。由於重複呼叫 |bheight|, 這是一個需要 $O(n^2)$ 時間的函數。請用組對的技巧推導出一個可在線性時間內判斷平衡的版本。
:::
:::{.exans}
定義：
```spec
balHeight :: RBTree -> (Bool, Nat)
balHeight = fork balanced bheight {-"~~."-}
```
{.nobreak}我們有 |balanced = fst . balHeight|.
顯然 |balHeight E = (True, 0)|.
考慮 |B t x u| 的狀況：
```spec
  balHeight (B t x u)
=   {- |balHeight| 之定義 -}
  (balanced (B t x u), bheight (B t x u))
=   {- |balanced| 與 |bheight| 之定義 -}
  (bheight t == bheight u && balanced t && balanced u,
   1 + (bheight t `max` bheight u))
=   {- 將 |balanced| 與 |bheight| 的呼叫取出 -}
  let  (bt,  ht)  = (balanced t, bheight t)
       (bu,  hu)  = (balanced u, bheight u)
  in   (ht == hu && bt && bu, 1 + (ht `max` hu))
=   {- |balHeight| 之定義 -}
  let  (bt,  ht)  = balHeight t
       (bu,  hu)  = balHeight u
  in   (ht == hu && bt && bu, 1 + (ht `max` hu)) {-"~~."-}
```

當輸入為 |R t x u| 的情況亦雷同。我們可推導出：
```spec
balHeight :: RBTree -> (Bool, Nat)
balHeight E          =  (True, 0)
balHeight (R t x u)  =  let  (bt,  ht)  = balHeight t
                             (bu,  hu)  = balHeight u
                        in   (ht == hu && bt && bu, (ht `max` hu))
balHeight (B t x u)  =  let  (bt,  ht)  = balHeight t
                             (bu,  hu)  = balHeight u
                        in   (ht == hu && bt && bu, 1 + (ht `max` hu)) {-"~~."-}
```
:::
:::

### 代換為最小標籤 --- 循環程式 {#sec:rep-minE}

下列函數 |minE| 曾出現在第 \@ref{sec:other-inductive-datatypes} 節中，找出一棵 |ETree| 中最小的值。
函數 |rep| 則可視為 |repl| 的簡單版，將樹中的每個標籤都代換成同一個值 |y|。
::: {.multicols}
::: {.mcol width="0.45\\textwidth"}
```haskell
minE :: ETree Int -> Int
minE (Tip x)    = x
minE (Bin t u)  = minE t `min` minE u {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```haskell
rep :: b -> ETree a -> ETree b
rep y (Tip _)   = Tip y
rep y (Bin t u) = Bin (rep y t) (rep y u) {-"~~."-}
```
:::
:::
給一棵樹 |t|, 我們要把 |t| 之中的每個標籤都代換成 |t| 的最小標籤。
直觀的做法是寫成 |let m = minE t in rep t m|.
如此一來，|t| 會被走訪兩次，第一次被|minE| 走訪以計算 |m|, 第二次由 |rep| 進行代換。
@Bird:84:Circular 提出挑戰：有可能在只把 |t| 走訪一次的情況下，完成上述工作嗎？

以下函數 |repmin| 同時傳回代換過後的樹，以及原樹中的最小標籤：
```spec
repmin :: ETree Int -> a -> (ETree a :* Int)
repmin y = fork (rep y) minE {-"~~."-}
```
{.nobreak}使用本節的技巧，讀者們應該已經可以為 |repmin| 導出如下的歸納定義：
```haskell
repmin y (Tip x)    =  (Tip y, x)
repmin y (Bin t u)  =  let  (t', m) = repmin y t
                            (u', n) = repmin y u
                       in (Bin t' u', m `min` n) {-"~~."-}
```
{.nobreak}該定義只將 |t| 走訪一次。然後我們定義：
```haskell
transform :: ETree Int -> ETree Int
transform t =  let (t', m) = repmin m t in t' {-"~~."-}
```
{.nobreak}函數 |transform| 用 |repmin| 算出 |t| 的最小標籤 |m|, 同時又用 |m| 來標記 |t|... 於是，似乎確實用一次走訪就完成了兩件事！這是怎麼做到的呢？

函數 |transform| 有個特殊之處：變數 |m| 既是 |repmin| 的傳回值，又是其參數。
這是一個*循環程式*(*circular program*)。
\index{circular program 循環程式}
這樣的程式之所以能正常終止，有賴於 Haskell 的範式順序/惰性求值（見第\@pageref{para:lazy-evaluation}頁）。實際上發生的事情如此：假設輸入為
```haskell
t = Bin  (Bin (Tip 4) (Tip 2))
         (Bin (Bin (Tip 3) (Tip 1)) (Tip 5))
```
{.nobreak}|repmin| 將輸入 |t| 走訪一遍，邊走邊建立了一個未算出的算式 |(4 `min` 2) `min` ((3 `min` 1) `min` 5)|.
該算式就是 |m| 的值，其實也可視作一棵樹，其結構和 |t| 一樣，只是把每個 |Bin| 代換成 |min|.
函數 |repmin| 的另一項工作是新建一棵樹 |t'|，該樹之中每個 |Tip| 的標籤都指到這個算式。
根據範式順序求值，這個算式還不用立刻被算出來。直到我們終於不得不算出它，例如當 |t'| 被傳回，我們要求電腦把 |t'| 印出來，或著有別的函數需檢查 |t'| 中的標籤時，該算式才被歸約成一個數字 --- 這需要把該算式走訪一遍。
（但，根據惰性求值，一但 |m| 被算成一個數字，下次使用 |m| 時就不再需要反覆計算了。）

需注意，雖然「|t|只被走訪一次」確實成立，這並不表示 |transform| 必然比老實將樹走訪兩次的程式快 --- 效率是個複雜的問題，本章將陸續談到更多。我的建議是：循環程式應視為有趣、優雅的謎題，而不是以效率為目的的程式設計技巧。

### 小結與提醒 {#sec:tupling-conclude}

「組對」的技巧讓函數多傳回一些值。我們可能藉此省下一些重複的計算，增進效率。

我們自然想問：給一個有重複計算、待改進的函數 |f|, 怎知道該讓它多傳回什麼值？
在本節的例子中，我們可由符號演算看出一些端倪：
將 |f| 的定義展開，辨識出被重複計算的子算式，這些子算式就可能用來與原函數組對。
但廣泛說來，「將一個函數或性質通用化」是編程與證明中最困難、最需要經驗、智慧的一步。
只要找到正確的通用化，例如 |steepsum| 或 |repTail|, 剩下的推導都可相當機械化地進行。
唯有「通用化」這一步，我們無法保證有任何機械化、公式化的方法可作為解決所有問題的萬靈丹 ---
否則編程就是一件可完全自動化的事情了。

雖然如此，我們仍希望基於符號演算的形式方法能給我們一定程度的幫助與指引。
程式語言研究的目標之一便是分辨出編程的過程中，哪些部分是瑣碎、機械化的，哪些部分是真正需要靈感與智慧的，並且盡量使用符號幫助，使我們在進行思考時有更多工具。

組對可用於減少走訪資料結構的次數，但這麼做並不見得有效率上的好處。
例如，以下函數計算一個串列中元素的平均值：
```spec
average xs = sum xs / length xs {-"~~."-}
```
{.nobreak}利用組對，我們可以另定義一個函數 |sumlen = fork sum length|,
並推導其歸納定義，在一次走訪中同時計算串列的和與長度：
```haskell
sumlen []      =  (0,0)
sumlen (x:xs)  =  let (s,l) = sumlen xs
                  in (x + s, 1 + l) {-"~~."-}
```
{.nobreak}然後平均便可定義成 |average' xs = let (s,l) = sumlen xs in s/l|.
```texonly
%函數 |average| 中，串列 |xs| 需要留在記憶體中的時間較長：|sum xs| 計算過後，|xs| 不能立刻被丟掉，而必須留在記憶體中，等著計算 |length xs|.
%而 |average'| 只走訪 |xs'| 一次，|xs| 可以邊走訪邊丟棄。
%\todo{Shall we mention this? Shall we run some experiments?}
```
然而，根據@HuIwasaki:97:Tupling，|average'| 通常比 |average| 慢。
兩者都是 $O(n)$ 的演算法。
函數 |sumlen| 在傳回值時會產生一個序對，該序對立刻被上層拆掉。
因此 |average'| 每處理一個元素耗費的時間較多，往往不如乾脆將 |xs| 走訪兩次。
@HuIwasaki:97:Tupling 認為需有更有效率的序對實作法，組對才是值得做的轉換。

:::{.exlist}
:::{.exer #ex:allpairs}
函數 |allpairs| 傳回輸入串列中任兩個元素（依其原本順序）形成的序對。
例如 |allpairs [1,2,3,4]| 可得到 |[(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]|。
```haskell
allpairs :: List a -> List (a :* a)
allpairs []      = []
allpairs (x:xs)  = map (\y -> (x,y)) xs ++ allpairs xs {-"~~."-}
```
{.nobreak}而 |maxdiff| 則計算一個串列中任兩元素前者與後者的最大差：
```haskell
maxdiff :: List Int -> Int
maxdiff = maximum . map (\(x,y) -> x - y) . allpairs {-"~~."-}
```
{.nobreak}當輸入串列長度為 |n|, 如此定義的 |maxdiff| 是一個需時 $O(n^2)$ 的演算法。
定義：
```spec
 mdm xs = (maxdiff xs, ???) {-"~~."-}
```
{.nobreak}找出 |???| 可能的值，使得 |mdm| 能在 $O(n)$ 時間之內完成計算。
你可假設以下性質：
```{.equation #eq:max-minus}
  & |maximum (map (x-) xs) = x - minimum xs| \mbox{~~.}
```
並假設 |maximum| 與 |minimum| 在空串列上的值分別為 |-infty| 與 |infty|.
:::
:::{.exans}
由 \@eqref{eq:max-minus} 我們推測：
```spec
mdm :: List Int -> (Int :* Int)
mdm xs = (maxdiff xs, minimum xs) {-"~~."-}
```
{.nobreak}我們試圖找出 |mdm| 的歸納定義。顯然 |mdm [] = (-infty, infty)|.
考慮歸納情況（令 |minus (x,y) = x-y|）：
```{.haskell .invisible}
minus (x,y) = x-y

mdmDer1 :: Int -> List Int -> (Int :* Int)
mdmDer1 x xs =
```
```haskell
      mdm (x:xs)
 ===    {- |mdm|, |maxdiff|, 與 |minimum| 之定義 -}
      (maximum (map minus (allpairs (x:xs))), x `min` minimum xs)
 ===  (  maximum (map minus (map (\y -> (x,y)) xs ++ allpairs xs)),
         x `min` minimum xs) {-"~~."-}
```
{.nobreak}集中焦點在序對的第一個元素：
```{.haskell .invisible}
mdmDer2 :: Int -> List Int -> Int
mdmDer2 x xs =
```
```haskell
      maximum (map minus (map (\y -> (x,y)) xs ++ allpairs xs))
 ===     {- 因 |map f (xs ++ ys) = map f xs ++ map f ys| (習題 \ref{ex:map-append}) -}
      maximum (  map minus (map (\y -> (x,y)) xs) ++
                 map minus (allpairs xs))
 ===     {- |map|-fusion -}
      maximum (map (x-) xs ++ map minus (allpairs xs))
 ===     {- 因 |maximum (xs ++ ys) = maximum xs `max` maximum ys| -}
      maximum (map (x-) xs) `max` maximum (map minus (allpairs xs))
 ===     {- 因 \eqref{eq:max-minus} -}
      (x - minimum xs) `max` maximum (map minus (allpairs xs))
 ===     {- |maxdiff| 之定義 -}
      (x - minimum xs) `max` maxdiff xs {-"~~."-}
```
{.nobreak}回到推導主體：
```{.haskell .invisible}
mdmDer3 :: Int -> List Int -> (Int :* Int)
mdmDer3 x xs =
```
```haskell
      mdm (x:xs)
 ===    {- 上述計算 -}
      ((x - minimum xs) `max` maxdiff xs , x `min` minimum xs)
 ===    {- 使用 |let| -}
      let (y, z) = (maxdiff xs, minimum xs)
      in ((x - z) `max` y, x `min` z)
 ===    {- |mdm| 之定義 -}
      let (y, z) = mdm xs
      in ((x - z) `max` y, x `min` z)  {-"~~."-}
```
{.nobreak}於是我們得知：
```haskell
mdm []      =  (minBound, maxBound)
mdm (x:xs)  =  let (y, z) = mdm xs
               in ((x - z) `max` y, x `min` z)  {-"~~."-}
```
:::
:::


## 累積參數 {#sec:accumulating-param}

在第 \@ref{sec:efficiency-basics} 節中，我們曾提及該處定義的 |reverse :: List a -> List a| 需要 $O(n^2)$ 的時間。是否有比較快的作法呢？

### 串列反轉與連接 {#sec:reversal-append}

下列函數 |revcat| 似乎比 |reverse| 更通用一些：它拿兩個參數 |xs| 與 |ys|, 不僅將 |xs| 反轉，還把 |ys| 接到反轉後結果的右邊：
^[|revcat| 為 ``reverse'' 與 ``concat'' 的簡寫。]
```haskell
revcat :: List a -> List a -> List a
revcat xs ys = reverse xs ++ ys {-"~~."-}
```
{.nobreak}原有的 |reverse| 可以視為 |revcat| 的特例 --- |reverse xs = revcat xs []|.
這裡是否也會出現*責任越大，能力越強*的現象：
看似做了較多事情的 |revcat| 其實反倒有比較有效率的實作呢？
我們試著演算看看！當 |xs := []|, 顯然 |revcat [] ys = ys|.
考慮 |xs := x:xs| 的情況：
```{.haskell .invisible}
revcatDer x xs ys =
```
```haskell
      revcat (x:xs) ys
 ===    {- |revcat| 之定義 -}
      reverse (x:xs) ++ ys
 ===    {- |reverse| 之定義 -}
      (reverse xs ++ [x]) ++ ys
 ===    {- |(++)| 之結合律 -}
      reverse xs ++ ([x] ++ ys)
 ===    {- |(++)| 與 |revcat| 之定義 -}
      revcat xs (x : ys) {-"~~."-}
```
{.nobreak}因此我們有了：
```spec
revcat []      ys = ys
revcat (x:xs)  ys = revcat xs (x:ys) {-"~~."-}
```
{.nobreak}我們看看 |revcat [1,2,3,4] []| 如何歸約：
```spec
   revcat (1:2:3:4:[]) []
=  revcat (2:3:4:[]) (1:[])
=  revcat (3:4:[]) (2:1:[])
=  revcat (4:[]) (3:2:1:[])
=  revcat [] (4:3:2:1:[])
=  [4,3,2,1] {-"~~."-}
```
{.nobreak}串列 |[1,2,3,4]| 中的元素一個個被搬到 |revcat| 的第二個參數中。這是一個常數時間內可完成的動作，而每個元素只會被搬動一次。因此當 |xs| 的長度是 |n|，|reverse xs ys| 可在 $O(n)$ 的時間內執行完畢！

我們剛看到的技巧和第 \@ref{sec:tupling} 節中的組對互為對偶。
在第 \@ref{sec:tupling} 節中，我們為了導出一個函數的較快版本，讓它多傳回一些資訊。
而在本節，我們則讓一個函數多吃些參數，多接受些資訊。
通常這些新介紹的參數用於「累積」計算到目前為止的結果，例如
在 |revcat| 中，參數 |ys| 存放被反轉到一半的串列。
因此這個技巧被稱作*累積參數*(*accumulating parameters*)\index{accumulating parameters 累積參數}。

很多情況下，累積參數的運用仰賴某些運算元的結合律。
觀察 |revcat| 的推導，關鍵的一步便是 |(++)| 的結合律。
它使我們能夠把 |(reverse xs ++ [x]) ++ ys| 轉換為 |reverse xs ++ ([x] ++ ys)|，將
|[x]| 往右搬，才能收回、累積到 |revcat| 的第二個參數 |ys| 中。

回顧起來，我們最初如何發明出 |revcat xs ys = reverse xs ++ ys| 這樣的定義呢？
一個解釋便是：|reverse| 之所以慢，是因為 |(++)| 的括號都括錯了方向，往左邊括了。
因此我們在右邊補一個 |(++ ys)|, 希望用 |(++)| 的結合律，將括號往右挪。

我們多看一個例子。以下函數 |tags| 傳回一棵 |ITree| 中所有的標籤：
```haskell
tags :: ITree a -> List a
tags Null          = []
tags (Node x t u)  = tags t ++ [x] ++ tags u {-"~~."-}
```
{.nobreak}和習題 \@ref{ex:ETree-tips} 的情況類似，當 |t| 是一棵向左傾斜的樹，|tags| 會需要 $O(n^2)$ 的時間。
例如，考慮這棵樹 |t| （以下將 |Node x Null Null| 簡寫為 |lv x|）：
```spec
  t = Node 7  (Node 6  (Node 4  (Node 2 (lv 1) (lv 3))
                       (lv 5)))
              (lv 8) {-"~~."-}
```
{.nobreak}將 |tags t| 展開（並為說明方便，將一些 |[]++[x]++[]| 化簡為 |[x]|），我們會得到：
```spec
 ((([1] ++ [2] ++ [3])  ++ [4]
                        ++ [5]) ++ [6]) ++ [7] ++ [8] {-"~~."-}
```
{.nobreak}這個式子的結構和 |t| 一樣，只是將 |Node x...| 都變為 |.. ++ [x] ++ ..|.
我們可看到 |(++[6])| 需要走過一個長度為 |5| 的串列，|(++[7])| 需要走過一個長度為 |6| 的串列。

為了避免 |(++)| 的重複走訪，我們在 |tags t| 的左邊補一個 |(++ys)|, 希望透過結合律改變括號的順序。我們定義：
```haskell
tagsAcc :: ITree a -> List a -> List a
tagsAcc t ys = tags t ++ ys {-"~~."-}
```
{.nobreak}利用 |(++)| 的結合律，讀者應不難導出如下的歸納定義：
```spec
tagsAcc Null          ys = ys
tagsAcc (Node x t u)  ys = tagsAcc t (x : tagsAcc u ys) {-"~~."-}
```
{.nobreak}之後我們便可重新定義 |tags t = tagsAcc t []|.
至於 |tagsAcc| 的效率如何呢？
如果將 |tagsAcc t ys| 展開，我們順利地得到：
```spec
 1 : (2 : (3 : (4 : (5 : (6 : (7 : (8 : ys))))))) {-"~~."-}
```

:::{.exlist}
:::{.exer #ex:tagsAcc}
由 |tagsAcc t ys = tags t ++ ys| 推導出上述的歸納定義。
:::
:::{.exans}
僅看 |t := Node x t u| 的狀況：
```{.haskell .invisible}
tagsDer1 :: a -> ITree a -> ITree a -> List a -> List a
tagsDer1 x t u ys =
```
```haskell
      tagsAcc (Node x t u) ys
 ===  tags (Node x t u) ++ ys
 ===  (tags t ++ [x] ++ tags u) ++ ys
 ===    {- |(++)| 的結合律 -}
      tags t ++ (x : tags u ++ ys)
 ===  tagsAcc t (x : tagsAcc u ys) {-"~~."-}
```
{.nobreak}我們可導出：
```spec
tagsAcc Null          ys = ys
tagsAcc (Node x t u)  ys = tagsAcc t (x : tagsAcc u ys) {-"~~."-}
```
:::
:::{.exer #ex:tagsAcc-2}
確認 |tagsAcc t ys| 確實是 |1 : (2 : (3 : (4 : (5 : (6 : (7 : (8 : ys)))))))|.
:::
:::{.exer #ex:ETree-tipsAcc}
接續習題 \@ref{ex:ETree-tips}，利用累積參數，推導出一個只需線性時間的 |tips :: ETree a -> List a|.
:::
:::{.exans}
定義 |tipsAcc t ys = tips t ++ ys|.
如果 |tipsAcc| 有個有效率的定義，我們可改定義 |tips t = tipsAcc t []|.
當 |t := Tip x|, |tipsAcc (Tip x) ys| 可直接展開為 |x:ys|.
當 |t := Bin t u|,
```{.haskell .invisible}
tipsAcc :: ETree a -> List a -> List a
tipsAcc t ys = tips t ++ ys

tipsAccDer1 :: ETree a -> ETree a -> List a -> List a
tipsAccDer1 t u ys =
```
```haskell
      tipsAcc (Bin t u) ys
 ===  (tips t ++ tips u) ++ ys
 ===    {- |(++)| 之結合律 -}
      tips t ++ (tips u ++ ys)
 ===  tipsAcc t (tipsAcc u ys) {-"~~."-}
```
{.nobreak}因此，
```spec
tipsAcc (Tip x)    ys = x : ys
tipsAcc (Bin t u)  ys = tipsAcc t (tipsAcc u ys) {-"~~."-}
```
:::
:::

### 由上到下的資訊流 {#sec:accum-info-flow}

前一節之中，我們用累積參數改變 |(++)| 結合的順序。
更廣泛說來，累積參數常有「增加一個由上到下的資訊流」的效果。

{title="遞增串列"} 下述函數 |ascending| 判斷一個串列是否為遞增：
```spec
ascending :: List Int -> Bool
ascending []      = True
ascending (x:xs)  = all (x <=) xs && ascending xs {-"~~."-}
```
{.nobreak}當輸入串列長度為 |n|, 這個定義需做 $O(n^2)$ 次比較。
習題 \@ref{ex:ascendingTuple} 曾考慮過一個定義類似的 |ascending|，並用組對的技巧得到一個時間複雜度為 $O(n)$ 的程式。本節則試試看改用累積參數！

這次我們使用如下的定義：
```spec
ascendBnd xs z = all (z<=) xs && ascending xs {-"~~."-}
```
{.nobreak}在嘗試推導 |ascendBnd| 之前，我們得先確定它是有用的 --- |ascending| 可以用 |ascendBnd| 定義出來。確實如此：|ascending xs = ascendBnd xs minBound|.

現在我們可以推導 |ascendBnd| 的歸納定義了。基底狀況如下：
```{.haskell .invisible}
ascendBndDerBase z =
```
```haskell
      ascendBnd z []
 ===   {- |ascendBnd| 之定義 -}
      all (z<=) [] && ascending []
 ===   {- |all| 與 |ascending| 之定義 -}
      True
```

歸納狀況的推導則會需要下述性質：
```{.equation #eq:lowerbound-strengthen}
  |z <= x && all (z <=) xs && all (x <=) xs {-"~~"-} ==> {-"~~"-} z <= x && all (x <=) xs {-"~~."-}|
```
{.nobreak}回顧起來，我們之所以那麼定義 |ascendBnd|, 正是希望利用 \@eqref{eq:lowerbound-strengthen} 將程式中的 |all (z<=) xs| 吸收掉。推導如下：
```{.haskell .invisible}
ascendBndDerInd z x xs =
```
```haskell
      ascendBnd z (x:xs)
 ===    {- |ascendBnd| 與 |ascending| 之定義 -}
      all (z<=) (x:xs) && all (x <=) xs && ascending xs
 ===    {- |all| 之定義 -}
      z <= x && all (z <=) xs && all (x <=) xs && ascending xs
 ===    {- 性質 \eqref{eq:lowerbound-strengthen} -}
      z <= x && all (x <=) xs && ascending xs
 ===    {- |ascendBnd| 之定義 -}
      z <= x && ascendBnd x xs {-"~~."-}
```

總結之，我們導出了下述定義：
```haskell
ascendBnd :: Int -> List Int -> Bool
ascendBnd z []      = True
ascendBnd z (x:xs)  = z <= x && ascendBnd x xs {-"~~."-}
```
{.nobreak}讀者可將之與最初的 |ascending| 比較。函數 |ascending| 的資訊流動只從串列尾到頭 --- |ascending (x:xs)| 的值需等待 |ascending xs| 的結果。但 |ascendBnd| 多了一個 \emph{由上到下}的資訊流動：如果 |ascendBnd z xs| 成立，參數 |z| 是 |xs| 所有元素的下界 (lower bound)，而該參數的值在每次遞迴呼叫時更新。

{title="深度標記"} 給定 |t :: ITree a|（型別 |ITree| 定義於第 \@ref{sec:user-defined-data} 節）, 下述函數 |depthsT t| 由左至右傳回樹中所有的元素，並標記其深度 --- 根部節點的深度為 |0|, 左右子樹中的節點的深度則是其原本深度加一：
```haskell
depths :: ITree a -> List (a :* Nat)
depths Null          =  []
depths (Node x t u)  =  map (id *** (Suc)) (depths t) ++ [(x,0)] ++
                        map (id *** (Suc)) (depths u) {-"~~."-}
```
{.nobreak}由於反覆使用 |map|, 當輸入樹有 |n| 個節點時，|depths| 最壞情況下需使用 $O(n^2)$ 個 |(Suc)|. 是否可能用累積參數讓它快一點呢？

和各種程式堆導與證明技巧一樣，使用累積參數的技巧時，最難的一步是如何設計那個通用版的函數。
我們的答案仍是\emph{讓符號為你工作}：許多時候我們可以藉由觀察算式、展開定義看出有哪些部分是可以取出、吸收、或累積的。在 |ascending| 的例子中，我們希望把 |all (x<=) xs| 吸收掉。
至於此處，如果試圖展開 |depths|, 我們會看到許多層 |map (id *** (Suc))| 被堆積在算式中等待被畫減。
如果我們在最外面套一個 |map (id *** (k +:))|:
```spec
depthsAcc t k = map (id *** (k +:)) (depths t) {-"~~."-}
```
也許有機會改變括號的順序，並將 |map (id *** (Suc))| 吸收到
|map (id *** (k +:))| 之中。

同樣地，在推導 |depthsAcc| 之前，我們得先確認 |depths| 是 |depthsAcc| 的特例。
確實，|depths t = depthsAcc t 0|.

然後我們可以開始推導 |depthsAcc| 了。基底狀況中，|depthsAcc Null k = []|.
考慮歸納狀況：
```{.haskell .invisible}
depthsAccDerInd x t u k =  
```
```haskell
      depthsAcc (Node x t u) k
 ===    {- |depthsAcc| 與 |depths| 之定義 -}
      map (id *** (k +:)) (  map (id *** (Suc)) (depths t) ++ [(x,0)] ++
                             map (id *** (Suc)) (depths u))
 ===    {- |map| 分配入 |(++)|, |map| 之定義 -}
      map (id *** (k +:)) (map (id *** (Suc)) (depths t)) ++ [(x,k)] ++
      map (id *** (k +:)) (map (id *** (Suc)) (depths u))
 ===    {- |map| 融合， |(***)| 融合 \eqref{eq:prod-fusion} -}
      map (id *** ((k +:) . (Suc))) (depths t) ++ [(x,k)] ++
      map (id *** ((k +:) . (Suc))) (depths u)
 ===    {- 對所有 |n|, 我們有 |k +: (Suc n) = Suc (k +: n)| -}
      map (id *** ((Suc k) +:)) (depths t) ++ [(x,k)] ++
      map (id *** ((Suc k) +:)) (depths u)
 ===    {- |depthsAcc| 與 |depths| 之定義 -}
      depthsAcc t (Suc k) ++ [(x,k)] ++ depthsAcc u (Suc k) {-"~~."-}
```
{.nobreak}因此我們得到
```haskell
depthsAcc :: ITree a -> Nat -> List (a :* Nat)
depthsAcc Null          k =  []
depthsAcc (Node x t u)  k =  depthsAcc t (Suc k) ++ [(x,k)] ++
                             depthsAcc u (Suc k) {-"~~."-}
```

同樣地，|depthsAcc| 的參數 |k| 是從上往下傳遞的資訊：它記錄著目前的深度，每往下一層就遞增一次。

:::{.exlist}
:::{.exer}
下述函數 |depthsT| 將一個 |ITree| 的深度標記在樹中：
```haskell
depthsT :: ITree a -> ITree (a :* Nat)
depthsT Null          = Null
depthsT (Node x t u)  = Node (x,0)  (mapI (id *** (Suc)) (depthsT t))
                                    (mapI (id *** (Suc)) (depthsT u)) {-"~~."-}
```
{.nobreak}其中 |mapI :: (a -> b) -> ITree a -> ITree b| 將函數作用在樹中的每個元素上（見習題 \@ref{ex:ITree-mapI}）。
同樣地，反覆使用 |mapI| 使得本程式需用 $O(n^2)$ 個 |(Suc)|.
請推導出一個只用 $O(n)$ 個 |(Suc)| 的程式。
:::
:::{.exans}
採用這個定義：
```spec
depthsTAcc t k = mapI (id *** (k +:)) (depthsT t) {-"~~."-}
```
我們可重定義 |depthsT t = depthsTAcc t 0|. 其餘的推導與 |depthsAcc| 類似。
:::
:::


:::{.exlist}
:::{.exer}
由於 |(++)| 的使用方式，本節導出的 |depthsAcc| 在最壞情況下的時間複雜度仍是 $O(n^2)$.
請再使用累積參數，導出一個時間複雜度為 $O(n)$ 的程式。
:::
:::{.exans}
採用這個定義：
```spec
depthsAcc' t k ys = depthsAcc t k ++ ys {-"~~."-}
```
:::
:::




### 尾遞迴 {#sec:tail-recursion}

關於第 \@ref{sec:reversal-append} 節的 |revcat| 有許多面向可談。
本節先用它帶出一個重要的觀念：尾遞迴。

從第 \@ref{ch:induction} 章起，我們常見的歸納定義形式如下：
::: {.multicols}
::: {.mcol width="0.5\\textwidth"}
```spec
f []      = ...
f (x:xs)  = ... f xs ... {-"~~."-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```spec
sum []      = 0
sum (x:xs)  = x + sum xs {-"~~."-}
```
:::
:::
右側的 |sum| 函數便是一個典型的例子。
我們通常必須對遞迴呼叫的結果做些加工。
例如此處 |sum xs| 的結果需要經過 |(x+)|, 才成為 |sum (x:xs)| 的值。
實作上，電腦在執行 |sum xs| 的程式碼前必須記下「|sum xs| 回傳後，必須回來執行 |(x+)|」這件事。
這可能用堆疊或著其他方式達成。
無論如何，當 |xs| 長度為 |n|, 便有大約 |n| 個這種「尚待完成的計算」被暫存著。
當 |xs| 被走訪到了基底狀況，這些暫存的計算才一個個被收回。

但 |revcat| 的情況卻有點不同。
觀察其程式碼，會發現遞迴呼叫 |revcat xs (x:ys)| 的結果本身就是其左手邊 |revcat (x:xs) ys| 的值，不需其他的加工：
```spec
revcat []      ys = ys
revcat (x:xs)  ys = revcat xs (x:ys) {-"~~."-}
```
{.nobreak}因此，|revcat| 的實作中，遞迴呼叫完成後，電腦不需回到原呼叫之處再執行什麼東西：最後的結果 |ys| 可直接傳回到最上層、第一個呼叫 |revcat| 的地方！
^[如果該語言的實作確實有做到這點，我們說它實作了*尾呼叫消除*(*tail call elimination*)或*尾呼叫最佳化*(*tail call optimisation*)。有些語言到了蠻晚的版本才支援這個最佳化。]

當一個函數 |f| 呼叫函數 |g| 時，如果該呼叫本身就是函數 |f| 最後的結果，並沒有針對傳回值的額外計算，我們將它稱之為一個*尾呼叫*(*tail call*)。
\index{tail call 尾呼叫}
此名稱的由來可能是因為該呼叫是一連串計算後「最尾端」的動作。
如果這是一個遞迴呼叫，則稱之為*尾遞迴*(*tail recursion*)。
\index{tail recursion 尾遞迴}

```texonly
%{
%format e1
%format e2
%format do = "\mathbf{do}"
%format od = "\mathbf{od}"
```
{title="尾遞迴與迴圈"}
函數語言中的尾遞迴程式和指令式語言中的迴圈有相當密切的關係。
回顧 |revcat [1,2,3,4] []| 的歸約過程：
```spec
   revcat (1:2:3:4:[]) []
=  revcat (2:3:4:[]) (1:[])
=  revcat (3:4:[]) (2:1:[])
=  revcat (4:[]) (3:2:1:[])
=  revcat [] (4:3:2:1:[])
=  [4,3,2,1] {-"~~,"-}
```
{.nobreak}其實看來就像是一個有兩個變數的迴圈，其中一個由 |1:2:3:4:[]| 逐漸縮短為 |[]|，另一個由 |[]| 逐步增長為 |4:3:2:1:[]|.
函數 |reverse| 的定義 |reverse xs = revcat xs []| 就是為這兩個變數設定初始值：如果要計算 |xs| 的反轉，兩變數應該分別初始化為 |xs| 與 |[]|.
在 |revcat| 的定義中，|revcat [] ys| 表示該迴圈在第一個變數為 |[]| 時終止，此時程式傳回 |ys|；而|revcat (x:xs) ys = revcat xs (x:ys)| 則指定了在迴圈的每一步中兩個變數的值如何改變。
函數 |reverse| 與 |revcat| 的組合相當於是這樣的一個指令式語言迴圈（假設 |xs| 與 |ys| 為變數，|XS| 為欲反轉的串列）：
^[|xs, ys := e1, e2| 將 |e1| 與 |e2| 兩個值同時給予 |xs| 與 |ys|; |do B -> S od| 表示一個迴圈，當 |B| 還成立時便反覆執行 |S|.]
```spec
xs, ys := XS, [];
do xs /= [] ->
   xs, ys := tail xs, head xs : ys
od ;
return ys
```
```texonly
%} %GCL
```
而該迴圈的恆式(loop invariant)是什麼呢？
正是 |reverse XS = reverse xs ++ ys| --- 右手邊就是 |revcat| 的定義。

一般說來，一個尾遞迴函數可視為一個迴圈，其參數就是迴圈中的變數。
遞迴呼叫時參數改變，相當於更新這些變數的值，其基底狀況則相當於迴圈的終止條件。
當我們為了計算某個函數 |f| 而設計了另一個較通用、可寫成尾遞迴的函數 |fAcc|,
|fAcc| 的定義(例如 |reverse xs ++ ys|)往往就是這個迴圈的*恆式*(*loop invariant*)。
\index{loop invariant 迴圈恆式}
在指令式程式推導的方法學中，設計一個迴圈最難之處便是決定其恆式。
如第 \@ref{sec:tupling-conclude} 節所言，一般來說，並沒有一個固定的方法讓我們由 |f| 找出 |fAcc|。
但我們仍可讓符號推演幫我們一些忙，並歸納出一些常見的模式。

{title="串列總和"}
累積參數的技巧常被用來推導尾遞迴程式（雖然累積參數的應用並不僅止於此）。
我們多看一個例子。如前所述，|sum| 函數每次被遞迴呼叫時會需要用堆疊或其他等價的方式記住每個 |(x+)|。是否能避免這麼做呢？
我們定義：
```haskell
sumAcc :: List Int -> Int -> Int
sumAcc xs y = y + sum xs {-"~~."-}
```
{.nobreak}如此定義 |sumAcc| 的直覺理由是：我們想用參數 |y| 存放累積的結果，希望利用 |(+)| 的結合律逐步把 |sum xs| 的結果搬入 |y| 中。
同樣地，一但找到了這個定義，之後的演算便相當日常、例行了。
我們先記下：|sum xs = sumAcc xs 0|.
接下來試圖導出 |sumAcc| 的歸納定義。
在基底情況中，我們會需要 |y + 0 = y|。
為了目睹結合律如何運作，我們看看 |xs := x:xs| 的狀況：
```spec
     sumAcc (x:xs) y
===  y + sum (x:xs)
===  y + (x + sum xs)
===    {- |(+)| 之結合律 -}
     (y+x) + sum xs
===  sumAcc xs (y+x) {-"~~."-}
```
{.nobreak}讀者可能發現我們之所以定義 |sumAcc xs y| 為 |y + sum xs|, 而不是 |sum xs + y|, 是為了在使用結合律的那一步之中讓 |x| 可以就近與 |y| 結合。
當然，|(+)| 也滿足交換律，因此兩個定義其實是一樣的。
當我們處理沒有交換律的運算元時，就得對這類細節更小心了。
總之，我們可導出以下的程式：
```spec
sumAcc []      y = y
sumAcc (x:xs)  y = sumAcc xs (y + x) {-"~~."-}
```
```texonly
%{
%format x0
%format x1
%format xN1 = "\Varid{x}_{N-1}"
%format xi = "\Varid{x}_{i}"
```
這可翻譯成下述的兩種迴圈之一。
左手邊的程式將串列 |XS| 加總，使用的兩個變數 |xs| 與 |y| 對應到 |sumAcc| 的兩個參數。
在右邊的程式中，我們假設輸入資料 |[x0, x1.. xN1]| 依序被存放在一個陣列 |X| 中。陣列有 |N| 個元素，其索引範圍為 |[0.. N-1]|.
我們把陣列視為索引到內容的函數，因此 |X i| 存放著 |xi|.
```texonly
%format do = "\mathbf{do}"
%format od = "\mathbf{od}"
```
::: {.multicols}
::: {.mcol width="0.5\\textwidth"}
```spec
xs, y := XS, 0;
do xs /= [] ->  y   := y + head xs ;
                xs  := tail xs
od ;
return y
```
:::
::: {.mcol width="0.45\\textwidth"}
```spec
i, y := 0, 0;
do i /= N ->  y  := y + X i ;
              i  := i + 1
od ;
return y
```
:::
:::
```texonly
%} %GCL
```
確實，這就是我們一般用指令式語言加總一個串列/陣列時的常見迴圈寫法：
由左到右走訪，用一個變數存放目前為止的和。
以往許多人可能都沒注意到：同樣是「將 |xs| 由左到右走一遍」，這個程式和 |sum xs| 是不同的演算法！
|sum [1,2,3,4]| 算出的是 |1 + (2 + (3 + (4 + 0)))|,
而上述的、我們常用的那個迴圈算出的是 |(((0 + 1) + 2) + 3) + 4|.
多虧 |(+)| 的結合律，它們剛好是一樣的。

{title="在迴圈中處理串列"}
在本節的結尾，我們更完整地討論一下歸納式的串列處理與迴圈的關係。初次閱讀的讀者可跳過本段。
假設某函數 |f :: List A -> B| 能寫成如下的形式：
```{.haskell .invisible}
tmp1 = undefined
 where
 e :: Int
 e = undefined
 oplus :: Bool -> Int -> Int
 oplus = undefined
```
```haskell
 f []      = e
 f (x:xs)  = x `oplus` f xs {-"~~,"-}
```
{.nobreak}其中 |e :: B|, |oplus :: A -> B -> B|, 此處不假設 |oplus| 滿足結合律。我們能用一個尾遞迴函數（或著說用一個迴圈）計算 |f| 嗎？直覺上，我們可用一個迴圈將串列從右往左走一遍，並用變數紀錄目前為止算出的值。確實，如果我們要求如下的規格：
```{.equation #eq:fold-loop}
|loop xs (f ys)| &|= f (xs ++ ys) {-"~~,"-}|
```
{.nobreak}（所以 |f xs = loop xs (f []) = loop xs e|）
並分析 |xs := []| 和 |xs := xs++[x]| 的情況如下：
::: {.multicols}
::: {.mcol width="0.4\\textwidth"}
```spec
    loop [] (f ys)
===   {- |loop| 之規格 -}
    f ([] ++ ys)
===   {- |(++)| 之定義 -}
    f ys {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```spec
    loop (xs++[x]) (f ys)
===   {- |loop| 之規格 -}
    f (xs ++ [x] ++ ys)
===   {- |(++)| 之結合律，|loop| 之規格 -}
    loop xs (f (x:ys))
=== loop xs (x `oplus` f ys) {-"~~."-}
```
:::
:::
可知如下定義的 |loop| 能滿足 \@eqref{eq:fold-loop}：
```spec
loop []           z = z
loop (xs ++ [x])  z = loop xs (x `oplus` z) {-"~~."-}
```
但從串列尾端取出元素較不方便。如果我們改用下式作為規格：
```{.equation #eq:fold-loop-rev}
|loop xs (f ys)| &|= f (reverse xs ++ ys) {-"~~,"-}|
```
{.nobreak}可推導出
```haskell
 loop []      z = z
 loop (x:xs)  z = loop xs (x `oplus` z) {-"~~."-}
```
{.nobreak}但此時要用 |loop| 計算出 |f xs|，得先將 |xs| 反轉：|f xs = loop (reverse xs) e|.
這具體印證了我們的觀察：在串列上歸納定義出的函數，處理元素的順序和通常寫法的迴圈是相反的。

```texonly
%{
%format x0
%format x1
%format xN1 = "\Varid{x}_{N-1}"
%format xN2 = "\Varid{x}_{N-2}"
%format xi = "\Varid{x}_{i}"
%format do = "\mathbf{do}"
%format od = "\mathbf{od}"
```
假設有 |N| 個元素的串列 |xs = [x0, x1 ... xN1]| 被*反過來*存放在陣列 |X| 之中，
意即 |X 0 = xN1|, |X 1 = xN2|, ... |X (n-1) = x0|.
前述的兩種 |loop| 函數都可在不同的詮釋下理解為如下的指令式程式。
```spec
i, z := 0, e;
do i /= N ->  z  := X i `oplus` z ;
              i  := i + 1
od ;
return z {-"~~."-}
```
```texonly
%} %GCL
```


### 更多尾遞迴範例 {#sec:tail-recursion-more}

我們多看些使用結合律推導出尾遞迴程式，並增進效率的例子。

{title="快速乘冪"} 說到結合律的應用，似乎不得不提作為經典例子的乘冪。我們在第 \@ref{sec:exp-binary-roll} 節中曾用二進位表示法導出一個用 $O(\log n)$ 個乘法計算 $b^n$ 的程式。
此處我們使用結合律推導出尾遞迴的版本。
回顧函數 |exp| 在第 \@ref{sec:induction-on-Nat} 節中的定義，乘冪便是連續的乘法。
我們定義以下的函數 |expAcc|，把 |exp b n| 乘上一個累積參數 |x|，希望將一些中間結果搬移到 |x| 中：
```spec
expAcc :: Nat -> Nat -> Nat -> Nat
expAcc b n x = x * exp b n {-"~~."-}
```
{.nobreak}如果 |expAcc| 有快速的定義，我們可以令 |exp b n = expAcc b n 1|.
然後我們針對 |n| 為零、|n| 為非零的偶數，以及 |n| 為奇數三種情況作分析。
當 |n := 0|, |expAcc b 0 x = x|. 當 |n| 為偶數時，可以被改寫成 |2*n|.
以下的推導中我們將 |exp b n| 寫成 $b^n$, 並假設它已有乘冪該有的各種性質：
```texonly
%{
%format exp b (n) = b "^{" n "}"
```
```{.haskell .invisible}
expAccDer1 :: Int -> Int -> Int -> Int
expAccDer1 b n x =
```
```haskell
      expAcc b (2 * n) x
 ===  x * exp b (2 * n)
 ===   {- 因 |exp b (m * n) = exp (exp b m) n| -}
      x * exp (exp b 2) n
 ===   {- |expAcc| 之定義，|exp b 2 = b * b| -}
      expAcc (b * b) n x {-"~~."-}
```
{.nobreak}當 |n| 是奇數，我們將它改寫成 |1+n|:
```{.haskell .invisible}
expAccDer2 :: Int -> Int -> Int -> Int
expAccDer2 b n x =
```
```haskell
      expAcc b (1 + n) x
 ===  x * exp b (1+n)
 ===    {- $\Varid{exp}$ 之定義 -}
      x * (b * exp b n)
 ===    {- |(*)| 之結合律 -}
      (x * b) * exp b n
 ===    {- |expAcc| 之定義 -}
      expAcc b n (x * b) {-"~~."-}
```
```texonly
%} %exp
```
將語法改寫成 Haskell 能接受的形式（例如將 |2 * n| 與 |n| 改寫成 |n| 與 |n `div` 2|）之後，我們得到這樣的程式：
```haskell
expAcc b 0 x  = x
expAcc b n x  | even  n = expAcc (b * b) (n `div` 2) x
              | odd   n = expAcc b (n-1) (x*b) {-"~~."-}
```
{.nobreak}確實，這是一般在指令式語言中快速計算乘冪的方式。
一個操作性的理解法是：|expAcc b n x| 開始執行後，第一個參數中總是存放著 |b| 的「|2| 的某個次方」的乘冪（$b$, $b^2$, $b^4$...）。只在 |n| 是奇數時，當時的 |b| 才會被乘入累積參數 |x| 之中。

:::{.exlist}
:::{.exer #ex:expAcc-loop}
本節的 |expAcc| 函數相當於怎樣的指令式語言迴圈？其迴圈恆式為何？
:::
```texonly
%{
%format do = "\mathbf{do}"
%format od = "\mathbf{od}"
%format fi = "\mathbf{fi}"
%format exp b (n) = b "^{" n "}"
```
:::{.exans}
假設我們要計算 |exp B N|:
```spec
b, n, x := B, N, 1;
do n /= 0 ->  if  even  n -> b, n := b * b, n `div` 2
              |   odd   n -> n, x := n - 1, x * b
              fi
od;
return x
```
{.nobreak}其迴圈恆式為 |exp B N = x * exp b n|.
```texonly
%} % GCL
```
:::
:::

:::{.exlist}
:::{.exer #ex:tail-recursion-length}
請推導出一個尾遞迴版本的 |length| 函數。
:::
:::

:::{.exlist}
:::{.exer #ex:tail-recursion-fact}
第 \@ref{sec:inductive-proof-on-Nat} 節中介紹了經典的階層函數：
```spec
fact :: Nat -> Nat
fact Zero     = 1
fact (Suc n)  = (Suc n) *: fact n {-"~~."-}
```
{.nobreak}請推導出一個尾遞迴版本。
您利用了關於 |(*:)| 的什麼性質？
最後的程式是否像是一個計算 |n| 階層的指令式語言迴圈呢？
:::
:::{.exans}
我們預期將利用 |(*:)| 的結合律。定義
|factAcc n y = y *: fact n|。
顯然 |factAcc Zero y = y|.
至於 |n := Suc n| 的狀況：
```spec
     factAcc (Suc n) y
===  y *: fact (Suc n)
===  y *: ((Suc n) *: fact n)
===    {- |(*:)| 之結合律 -}
     (y *: (Suc n)) *: fact n
===  factAcc n (y *: (Suc n)) {-"~~."-}
```
{.nobreak}因此我們有了下述定義。由於 |fact n = factAcc n 1|.
這相當於右邊的迴圈：
```texonly
%{
%format do = "\mathbf{do}"
%format od = "\mathbf{od}"
```
:::{.multicols}
:::{.mcol width="0.5\\textwidth"}
```spec
factAcc Zero     y = y
factAcc (Suc n)  y =
   factAcc n (y *: (Suc n)) {-"~~."-}
```
:::
:::{.mcol width="0.5\\textwidth"}
```spec
n, y := N, 0;
do n /= 0 -> n, y := n-1, y * n od;
return y {-"~~."-}
```
:::
:::
```texonly
%} %GCL
```
在推導 |factAcc| 的歸納定義時，我們不僅用到 |(*:)| 的結合律，也用到了 |y *: 1 = y|.
:::
:::

:::{.exlist}
:::{.exer #ex:mulAcc-Ologm}
第 \@ref{sec:induction-on-Nat} 節中把乘法定義為連續的加法。
確實，一些早期、簡單的微電腦中沒有專做乘法的電路，只能以加法實作乘法。
但如果有乘以二、除以二、以及判斷一個數字是奇數或偶數的指令（都是簡單的位元運算），我們只需 $O(\log m)$ 個加法即可計算 |m * n|. 定義：
```spec
mulAcc m n k = k + m * n {-"~~."-}
```
{.nobreak}請推導出一個只使用加減法、乘以二、除以二、奇偶判斷，並在 $O(\log m)$ 的時間內算出 |mulAcc m n k| 的歸納定義。這個定義能被改寫成一個迴圈嗎？其恆式為何？
:::
:::{.exans}
針對 |m| 做分析。基底情況中，|mulAcc 0 n k = k + 0 * n = k|.
當 |m| 為非零的偶數，可被改寫為 |2 * m| 並演算如下：
```{.haskell .invisible}
mulAccDer1 :: Int -> Int -> Int -> Int
mulAccDer1 m n k =
```
```haskell
      mulAcc (2*m) n k
 ===  k + (2*m) * n
 ===   {- |(*)| 之交換律與結合律 -}
      k + m * (2 * n)
 ===  mulAcc m (2*n) k {-"~~."-}
```
{.nobreak}當 |m| 為奇數，可被改寫為 |1+m|, 並演算如下：
```spec
      mulAcc (1+m) n k
 ===  k + (1+m) * n
 ===    {- |(*)| 分配進入 |(+)| -}
      k + n + m * n
 ===    {- |(+)| 之結合律，|mulAcc| 之定義 -}
      mulAcc m n (k + n) {-"~~."-}
```
{.nobreak}因此我們得到：
```haskell
mulAcc 0 n k  = k
mulAcc m n k  | even n  = mulAcc (m `div` 2) (2*n) k
              | odd n   = mulAcc (m - 1) n (k + n) {-"~~."-}
```
{.nobreak}如果改寫成計算 |M * N| 的迴圈，其恆式為 |M * N = k + m * n|.
:::
:::

:::{.exlist}
```texonly
%{
%format exp b (n) = b "^{" n "}"
```
:::{.exer #ex:dtoN}
下述函數 |dtoN| 將一個以串列表達的十進位數字轉成自然數。
例如 |dtoN [4,1,6,0] = 4160|:
```spec
dtoN :: List Nat -> Nat
dtoN []      = 0
dtoN (d:ds)  = d * exp 10 (length ds) + dtoN ds {-"~~."-}
```
{.nobreak}其中 |length ds| 的反覆計算使得 |dtoN| 成為一個需時 $O(n^2)$ 的演算法（|n| 為輸入串列的長度）。

  1. 使用組對的技巧，導出一個能在 $O(n)$ 時間內計算 |dtoN| 以及一些其他輔助結果的函數。
  2. 使用累積參數，導出一個能在 $O(n)$ 時間內計算 |dtoN| 的尾遞迴函數。**提示**：可試試看用這樣的定義 |dtoNAcc ds n = ..n.. + dtoN ds|.


```{.haskell .invisible}
dtoN [] = 0
dtoN (d:ds) = d * exp 10 (length ds) + dtoN ds
```
:::
:::{.exans}
要使用組對避免重複計算，我們可以定義一個函數同時傳回 |dtoN ds| 以及 |10| 的 |length ds| 次方。
```spec
dtoNT :: List Nat -> (Nat :* Nat)
dtoNT ds = (dtoN ds, exp 10 (length ds)) {-"~~."-}
```
{.nobreak}我們可輕易導出：
```haskell
dtoNT []      = (0,1)
dtoNT (d:ds)  = (d * t + n, 10 * t) {-"~~,"-}
  where (n,t) = dtoNT ds {-"~~."-}
```
{.nobreak}若使用累積參數，可定義
```spec
dtoNAcc ds n = n * exp 10 (length ds) + dtoN ds {-"~~."-}
```
{.nobreak}若有歸納定義，我們可令 |dtoN ds = dtoNAcc ds 0|.
基底狀況為 |dtoNAcc [] n = n|.
至於 |ds := d : ds| 的情況可演算如下：
```{.haskell .invisible}
dtoN'der1 d ds n =
```
```haskell
      dtoNAcc (d : ds) n
 ===  n * exp 10 (length (d:ds)) + dtoN (d:ds)
 ===  n * exp 10 (length (d:ds)) + d * exp 10 (length ds) + dtoN ds
 ===    {- |length| 與乘冪之定義 -}
      n * 10 * exp 10 (length ds) + d * exp 10 (length ds) + dtoN ds
 ===    {- 算數運算 -}
      (n * 10 + d) * exp 10 (length ds) + dtoN ds
 ===    {- |dtoNAcc| 之定義 -}
      dtoNAcc ds (n * 10 + d) {-"~~."-}
```
{.nobreak}可推導出：
```haskell
dtoNAcc []      n = n
dtoNAcc (d:ds)  n = dtoNAcc ds (n * 10 + d) {-"~~."-}
```
```texonly
%} %exp
```
:::
:::

{title="多個累積參數"}
我們以一個稍微複雜的例子結束本節。給定以下函數：
^[|masc| 為 ``mostly ascending'' 的縮寫。這個函數大致上遞增，但偶爾會掉下來一點點。]
```spec
masc :: Nat -> Nat
masc 0            = 1
masc (2 * n)      = 2 * masc n
masc (1 + 2 * n)  = n + masc n {-"~~."-}
```
```{.haskell .invisible}
masc :: Int -> Int
masc 0  = 1
masc n  | even  n = 2 * masc (n `div` 2)
        | odd   n =  (n `div` 2) + masc (n `div` 2) {-"~~."-}
```
我們想用累積參數的技巧，推導出一個以尾遞迴計算 |masc n| 的演算法。
最難的一步總是尋找一個合適的通用化。
我們試著展開 |masc|, 看看是否能找到什麼規律。
以 |masc 43| 為例：
```spec
   masc 43
=  21 + masc 21
=  21 + 10 + masc 10
=  31 + masc 10
=  31 + 2 * masc 5
=  31 + 2 * (2 + masc 2)
=  35 + 2 * masc 2
=  35 + 4 * masc 1
=  35 + 4 * 1
=  39 {-"~~."-}
```
{.nobreak}我們發現式子總能展開成為 |a + b * masc n| 的形式。
因此我們定義
```spec
mascAcc :: Nat -> Nat -> Nat -> Nat
mascAcc n a b = a + b * masc n {-"~~."-}
```
{.nobreak}但在開始推導 |mascAcc| 前，我們得先確定 |masc| 能由 |mascAcc| 算得出來。
幸好，我們可以讓 |masc n = mascAcc n 0 1|.

現在我們試著尋找 |mascAcc| 的尾遞迴定義。
當 |n := 0|, |mascAcc 0 a b = a + b|.
當 |n| 為非零的偶數，可以將它代換為 |2 * n|。我們推導：
```{.haskell .invisible}
mascAccDer1 :: Int -> Int -> Int -> Int
mascAccDer1 n a b =
```
```haskell
      mascAcc (2*n) a b
 ===  a + b * masc (2 * n)
 ===   {- |masc| 之定義 -}
      a + b * 2 * masc n
 ===  mascAcc n a (2 * b) {-"~~."-}
```
{.nobreak}而當 |n| 為奇數，可以寫成 |1 + 2 * n| 的形式：
```{.haskell .invisible}
mascAccDer2 :: Int -> Int -> Int -> Int
mascAccDer2 n a b =
```
```haskell
      mascAcc (1+2*n) a b
 ===  a + b * masc (1 + 2 * n)
 ===    {- |masc| 之定義 -}
      a + b * (n + masc n)
 ===    {- |(*)| 分配入 |(+)|, |(+)| 之結合律 -}
      (a + b * n) + b * masc n
 ===  mascAcc n (a + b * n) b {-"~~."-}
```
{.nobreak}因此我們有了如下的尾遞迴定義：
```haskell
mascAcc 0 a b  = a + b
mascAcc n a b  | even  n = mascAcc (n `div` 2) a (2 * b)
               | odd   n = mascAcc (n `div` 2) (a + b * (n `div` 2)) b {-"~~."-}
```
{.nobreak}在推導 |mascAcc| 的過程中使用了各種四則運算的性質，但總之目標是將式子整理回 |a + b * masc n| 的形式，以便收回成為 |mascAcc|。

:::{.exlist}
:::{.exer #ex:tail-recursion-fusc}
本題來自@Kaldewaij:90:Programming. 給定以下函數：
```spec
fusc :: Nat -> Nat
fusc 0            = 0
fusc 1            = 1
fusc (2 * n)      = fusc n
fusc (1 + 2 * n)  = fusc n + fusc (1 + n)
```
```{.haskell .invisible}
fusc :: Int -> Int
fusc 0  = 0
fusc 1  = 1
fusc n  | even  n = fusc (n `div` 2)
        | odd   n = fusc (n `div` 2) + fusc (1 + (n `div` 2))
```
請推導出一個計算 |fusc| 的尾遞迴程式。
**提示**: 以 |fusc 78| 為例展開，看是否能找到什麼規律。
:::
:::{.exans}
由於我們展開的式子都有 |a * fusc n + b * fusc (1 + n)| 的形式，
定義
```spec
 fuscAcc n a b = a * fusc n + b * fusc (1 + n) {-"~~."-}
```
{.nobreak}如果 |fuscAcc| 有歸納定義，我們可令 |fusc n = fuscAcc n 1 0|.

為推導 |fuscAcc|, 針對 |n| 做分析。
當 |n := 0|, |fuscAcc 0 a b = b|.
當 |n| 為非零偶數，可被改寫為 |2 * n|:
```{.haskell .invisible}
fuscAccDer1 :: Int -> Int -> Int -> Int
fuscAccDer1 n a b =
```
```haskell
      fuscAcc (2 * n) a b
 ===  a * fusc (2 * n) + b * fusc (1 + 2 * n)
 ===    {- |fusc| 之定義 -}
      a * fusc n + b * (fusc n + fusc (1 + n))
 ===    {- 四則運算 -}
      (a + b) * fusc n + b * fusc (1 + n)
 ===  fuscAcc n (a + b) b {-"~~."-}
```
{.nobreak}當 |n| 為奇數，也就是可改寫為 |1 + 2 * n| 的形式時：
```{.haskell .invisible}
fuscAccDer2 :: Int -> Int -> Int -> Int
fuscAccDer2 n a b =
```
```haskell
      fuscAcc (1 + 2 * n) a b
 ===  a * fusc (1 + 2 * n) + b * fusc (2 + 2 * n)
 ===  a * fusc (1 + 2 * n) + b * fusc (2 * (1 + n))
 ===    {- |fusc| 之定義 -}
      a * (fusc n + fusc (1 + n)) + b * fusc (1 + n)
 ===    {- 四則運算 -}
      a * fusc n + (a + b) * fusc (1 + n)
 ===  fuscAcc n a (a + b) {-"~~."-}
```
{.nobreak}因此我們有了如下的程式：
```haskell
fuscAcc 0 a b  = b
fuscAcc n a b  | even  n = fuscAcc (n `div` 2) (a + b) b
               | odd   n = fuscAcc (n `div` 2) a (a + b) {-"~~."-}
```
:::
:::

:::{.exlist}
:::{.exer #ex:mapAcc}
我們能以尾遞迴的方式做 |map f| 嗎？
如果以 |mapAcc f xs ys| |= ys ++ map f xs| 為規格, 我們會導出如下的歸納定義：
```spec
mapAcc f []      ys = ys
mapAcc f (x:xs)  ys = mapAcc f xs (ys++[f x]) {-"~~."-}
```
但重複的 |(++ [f x])| 需要 $O(n^2)$ 的時間。
請問用什麼樣的規格才能導出下面的歸納定義呢？
```spec
mapAcc f []      ys = reverse ys
mapAcc f (x:xs)  ys = mapAcc f xs (f x : ys) {-"~~."-}
```
:::
:::{.exans}
使用如下的規格：
```haskell
mapAcc :: (a -> b) -> List a -> List b -> List b
mapAcc f xs ys = reverse ys ++ map f xs {-"~~."-}
```
{.nobreak}因此 |mapAcc f [] ys = reverse ys|. 而 |xs := x : xs| 的情況推導如下：
```{.haskell .invisible}
mapAccDer1 f x xs ys =
```
```haskell
      mapAcc f xs ys
 ===  reverse ys ++ map f (x:xs)
 ===  reverse ys ++ (f x : map f xs)
 ===  (reverse ys ++ [f x]) ++ map f xs
 ===  reverse (f x : ys) ++ map f xs
 ===  mapAcc f xs (f x : ys) {-"~~."-}
```
:::
:::

### 尾遞迴的效率考量 {#sec:tail-recursion-efficiency}

如前一節所述，歸納定義的 |sum| 需用堆疊（或其他功能相當的機制）記下每個遞迴呼叫的結果該怎麼加工。
這會佔用與輸入串列長度成正比的額外空間，相當不理想 --- 直覺上，「將一個串列加總」應該是只需定量的額外空間即可完成的計算。
尾遞迴的 |sumAcc| 則只需用一個變數存放目前為止的總和，當串列走訪到底，可直接將這個總和傳到最上層，似乎合理多了。
因此，在以效率為考量的函數語言程式庫中，諸如加總、算最小值等等的函數幾乎都是以尾遞迴方式寫成的。
大部分函數語言使用*及早求值* --- 在呼叫一個函數之前，總是把其參數先算成範式（見第\@ref{sec:evaluation}節，第\@pageref{para:lazy-evaluation}頁）。
對這些語言來說，在上述場合使用尾遞迴函數確實只使用了定額的額外空間，效果相當好。

但對使用惰性求值的 Haskell 來說，情況又更複雜一些 ---
若以分析工具實測，我們會發現純以本章的方式寫出的 |sumAcc| 仍用了和串列長度成正比的記憶體空間！
這是怎麼回事呢？
如前所述，|sumAcc [1,2,3,4...] 0| 的值是 |((((0 + 1) + 2) + 3) + 4) + ...|.
串列越長，這個式子越長。
根據惰性求值的原則，Haskell 不拖到被強迫求值的最後一刻是不會將算式歸約的。
因此在走訪串列的過程中，|0+1| 不會歸約成 |1|, |(0 + 1) + 2| 不會歸約成 |3|...
這個大算式就這麼存放在記憶體中。
直到整個串列被走訪完，|sumAcc| 的呼叫者要檢查其傳回值了（可能是要將它印出來，或著做樣式配對），這個大算式才又一步步被化簡成一個單一數值。

為改善這類情況下的效率，Haskell 提供了一些方法讓我們早點把一些數值強迫算成範式。
例如在資料型別上標注某些欄位為「嚴格(strict)」的、使用內建函數 |seq| 將數值歸約、或甚至使用更低階、屬於特定編譯器的「無盒型別(unboxed type)」等等。
對實務導向的 Haskell 編程員來說這些都是實用的技巧，只是已超出本書的範疇。

如果函數傳回的不是數值，而是結構化的資料，而程式語言支援惰性求值，情形又有所不同。
如習題 \@ref{ex:mapAcc} 中所見，我們可用尾遞迴的方式做 |map f|:
```spec
mapAcc f []      ys = reverse ys
mapAcc f (x:xs)  ys = mapAcc f xs (f x : ys) {-"~~."-}
```
{.nobreak}乍看之下，這個程式的問題似乎是需要多做一次 |reverse|。
但這可能並不很嚴重：|reverse| 也可用 |revcat| 實作，在線性時間內完成。
該定義和原歸納定義的 |map f| 的最大差別是：|mapAcc f| 需*等到輸入串列整個被走訪完畢後才會開始傳回第一個結果*。而回顧 |map f| 的歸納定義：
```spec
map f []      = []
map f (x:xs)  = f x : map f xs {-"~~,"-}
```
{.nobreak}歸納狀況中，|f x : ...| 可在走訪到 |x| 時便先產生。考慮這樣的程式：
|length . filter p . map f|。根據惰性求值，|f x : ...| 會立刻被 |filter| 與 |length| 接收，然後才開始計算 |map f xs|. 因此 |map f| 回傳的中間串列其實並不會被完整地產生。
在大部分情況下，歸納定義的 |map f| 是比尾遞迴的 |mapAcc f| 更有效率的函數。
在許多情形中，*早點產生部分的結果、早點讓它被使用掉*，會是在空間與時間上都更有效率的做法。

### 函數作為串列 {#sec:difference-list}

既然說到串列反轉，本節延伸介紹一個相關且相當有用的技巧。
回顧 |revcat| 的尾遞迴定義，若將最後一個參數省去，其定義可改寫成：
```spec
revcat :: List a -> (List a -> List a)
revcat []      = id
revcat (x:xs)  = revcat xs . (x:) {-"~~."-}
```
{.nobreak}|revcat| 是一個傳回 |List a -> List a| 的函數。
在基底狀況，|revcat []| 傳回 |id|.
歸納狀況中，|revcat xs| 傳回的函數和 |(x:)| 組合在一起。
這和 |reverse| 其實很像：在基底狀況，|reverse []| 傳回空串列 |[]|,
歸納狀況中，|reverse (x:xs)| 傳回 |reverse xs ++ (x:[])|。
好像把空串列代換成 |id|, 把 |(++)| 變成 |(.)|, 我們就得到 |revcat| 了。

這令我們聯想：有沒有可能把 |List a -> List a| 視為串列的另一種表示法，
其中 |id| 就是空串列，而串列連接就是 |(.)| 呢？
定義：
```haskell
type DList a = List a -> List a {-"~~,"-}
```
{.nobreak}一個型別為 |DList a| 的函數 |f| 表示一個「尾段尚未確定」的串列 ---
餵給它一個尾巴 |ys|, |f ys| 便會傳回一個真正的串列。
若 |xs| 是一個型別為 |List a| 的串列， |(xs ++)| 便是如此的一個 |DList a|.
要將一個 |DList a| 轉成 |List a|, 則只需將 |[]| 傳進去即可。
下列兩個函數幫我們在這兩種表示法之間作轉換：
:::{.multicols}
::: {.mcol width="0.5\\textwidth"}
```haskell
toDList :: List a -> DList a
toDList xs = (xs ++) {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```haskell
toList :: DList a -> List a
toList xs = xs [] {-"~~."-}
```
:::
:::

空串列被轉換成 |([]++)|, 化簡一下之後確實得到了 |id|.
「含一個單一元素 |x|」的 |DList| 可寫成 |(x:)| ---
給任何串列，|(x:)| 把 |x| 接到其最左邊。

兩個 |DList a| 如何連接在一起呢？使用函數組合 |(.)|。
確實，|(xs++) . (ys ++)| 是一個接收任一個尾段 |ws|, 傳回 |xs ++ (ys ++ ws)| 的函數。
|DList| 版本的 ``cons'' 建構元則可定義成
% 我們可定義 |DList| 版本的空串列與 ``cons'' 建構元如下：
:::{.multicols}
::: {.mcol width="0.5\\textwidth"}
```haskell
nil :: DList a
nil = id {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```haskell
cons :: a -> DList a -> DList a
cons x xs = (x:) . xs {-"~~."-}
```
:::
:::

|List| 上的 |(++)| 若往左結合，效率會較不好。
例如 |(xs ++ ys) ++ zs| 會需要把 |xs| 走訪兩次。
|DList| 的情況呢？
考慮 |((xs ++) . (ys ++)) . (zs ++)|，其中左邊的兩個 |DList| 被括在一起。
我們演算看看給了一個尾端 |ws| 後的情況：
```spec
     ((xs ++) . (ys ++)) . (zs ++) $ ws
===    {- |(.)| 之定義 -}
     (xs ++) . (ys ++) $ zs ++ ws
===    {- |(.)| 之定義 -}
     (xs ++) $ ys ++ (zs ++ ws)
===  xs ++ (ys ++ (zs ++ ws)) {-"~~."-}
```
{.nobreak}由於 |(.)| 的定義，即使 |(xs ++) . (ys ++)| 先被組合在一起，我們仍得到括號往右括的 |xs ++ (ys ++ (zs ++ ws))|！

我們多研究一個例子。
在習題 \@ref{ex:ETree-tips} 中，給定一個 |ETree a|, 我們想傳回其所有的標記。
如果寫成 |tips (Bin t u) = tips t ++ tips u|，當樹往左邊傾斜時，程式會需要 $O(n^2)$ 的時間。
但如果我們改用 |DList|:
```spec
tipsD :: ETree a -> DList a
tipsD (Tip x)    = (x:)
tipsD (Bin t u)  = tipsD t . tipsD u {-"~~."-}
```
{.nobreak}上述函數會邊走訪輸入的樹，邊產生一個結構與輸入樹相同的 |DList|。
例如，考慮如下的樹：
```spec
t = Bin  (Bin  (Bin (Tip 5) (Tip 4))
               (Bin (Tip 3) (Tip 2)))
         (Tip 1){-"~~,"-}
```
{.nobreak}|tipsD t| 將會是 |(((5:). (4:)) . ((3:) . (2:))) . (1:)| -- 結構和 |t| 相同，只是將 |t| 的每個 |Tip x| 代換成 |(x:)|, 每個 |Bin| 代換成 |(.)|.
但當我們傳一個空串列進去，這個由 |(x:)| 和 |(.)| 形成的「樹」將被走訪一遍，並在線性時間內得到 |5:4:3:2:1:[]|。
事實上，如果我們為 |tipsD| 補一個參數並展開，我們將得到和習題 \@ref{ex:ETree-tipsAcc} 中一樣的結果。
有了 |tipsD|, 我們可將原有的 |tips| 改定義為 |tips = toList . tipsD|, 或著 |tips t = tipsD t []|.

@Hughes:86:Novel

:::{.exlist}
:::{.exer #ex:deepestAux}
在習題 \@ref{ex:deepest} 中，我們使用組對可能得到一個型別為 |ETree a -> (List a, Nat)| 的函數。該函數仍需要 $O(n^2)$ 的時間連接串列（其中 $n$ 為輸入樹的大小）。
請設計一個 $O(n)$ 的演算法。
:::
:::{.exans}
假設習題 \@ref{ex:deepest} 中推導出的函數為
|dd :: ETree a -> (List a, Nat)|. 我們定義：
```spec
ddD :: ETree a -> (DList a, Nat)
ddD t = let (xs, n) = dd t in ((\zs -> xs++zs), n) {-"~~."-}
```
{.nobreak}有了 |ddD| 後，我們可改定義 |dd t = let (f, n) = ddD t in (f [], n)|.

試著推導 |ddD| 的歸納定義，不難得到 |ddD (Tip x) = ((x:), 0)|.
考慮 |ddD (Bin t u)|, 為計算方便將 |dd| 改寫為 |if|-|then|-|else| 之形式：
```{.haskell .invisible}
-- ddDBin :: a -> (List a -> List a, Int)
ddDBin t u =
```
```haskell
      ddD (Bin t u)
 ===    {- |ddD| 之定義 -}
      let (xs, n) = dd (Bin t u) in ((xs++), n)
 ===    {- |dd| 之定義 -}
      let  (xs, m) = dd t
           (ys, n) = dd u
      in (  ((if m < n then xs else if m == n then xs ++ ys else ys)++),
            1 + (m `max` n))
 ===    {- 函數應用分配入 |if| -}
      let  (xs, m) = dd t
           (ys, n) = dd u
      in (  if m < n then (xs++) else if m == n then (xs ++ ys ++) else (ys++),
            1 + (m `max` n))
 ===    {- 抽出 |(xs++)| 與 |(ys++)| -}
      let  (f, m) = (let (xs, m) = dd t in ((xs++), m))
           (g, n) = (let (ys, n) = dd u in ((ys++), n))
      in (  if m < n then f else if m == n then f . g else g,
            1 + (m `max` n))
 ===    {- |ddD| 之定義 -}
      let  (f, m) = ddD t
           (g, n) = ddD u
      in (  if m < n then f else if m == n then f . g else g,
            1 + (m `max` n)) {-"~~."-}
```
{.nobreak}因此我們得到：
```haskell
ddD (Tip x)    = ((x:), 0)
ddD (Bin t u)  | m <  n  = (f, 1 + n)
               | m == n  = (f . g, 1 + n)
               | m >  n  = (g, 1 + m) {-"~~,"-}
  where ((f,m),(g,n)) = (ddD t, ddD u) {-"~~."-}
```
:::
:::
