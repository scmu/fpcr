``` {.haskell .invisible}

{-# LANGUAGE TypeOperators #-}
module Chapters.Semantics where

import Prelude ()
import Control.Arrow ((***))
import Common.MiniPrelude hiding (exp, length, take, drop, gcd)
```

# 關於語意的基本概念 {#ch:semantics}

第\@ref{ch:basics}章介紹了函數語言的基礎概念，第\@ref{ch:induction}章談了歸納定義與證明。我們將運用這些知識在第\@ref{ch:derivation}章之中推導一些程式、解一些編程問題。但在那之前，我們得暫緩一下，釐清一些和語意相關的概念。

語意(semantics)\index{semantics 語意}一詞由語言學中借用而來。
語意學是關於字句、詞語的意思的研究。一段程式的「意思」為何？
在電腦技術發展的早期這似乎不是個問題。
當時，「程式語言」只是屬於某台特定型號電腦的指令集，指令的意思就如同其操作手冊所說。
若有疑義，用電腦執行看看就知道了。
隨著技術發展，同一個程式語言可在不同電腦上執行，各廠商、研究機構都可以實作同一語言的編譯器。
同時，實用性質的程式語言也發展得更加複雜，一個程式語言中常有不太能憑直覺理解的細微處。
我們因而需要有個不依賴特定硬體、特定編譯器，也可討論程式語言的「意思」的方法。
不僅可作為各家實作程式語言的依據，也方便大家溝通：每當我們設計新的語言、符號，我們也常需要釐清它的語意是什麼。

描述語意的方式有許多種。本書目前為止其實在不知不覺中混用了兩種語意：指稱語意談一個程式*是什麼*，操作語意談一個程式*做什麼*。以下我們以非常粗略的方式介紹它們。

## 指稱語意 {#sec:denotational-semantics}

*指稱語意*(denotational semantics)\index{semantics 語意!denotational 指稱語意}談一個程式*是什麼*。
在我們的討論範圍中，有堅實基礎、有不含糊的定義的東西只有數學物件。
因此，指稱語意試圖把程式語言對應到數學物件。
最簡單的指稱語意可能是基於集合論的：把型別視為集合，把程式語言中的函數視為集合論中的函數。
例如，|Nat| 便是自然數的集合；|(A * B)| 是 |A| 與 |B| 的笛卡兒積：
^[在更嚴謹的說法中，我們通常用一個*語意函數*$\llbracket\_\rrbracket$將語法對應到其意義。因此我們會說 $\llbracket |A*B| \rrbracket = \llbracket |A| \rrbracket \times \llbracket |B| \rrbracket$. 此處採用較不正式的說法。]
```equation
    |(A * B)| ~&= \{ (a,b) \mid a \in |A|, b \in |B| \} \mbox{~~.}
```
{.nobreak}但函數又是什麼呢？集合論中，一個型別為 |A -> B| 的函數可視為 |A * B| 的一個子集；若 |f x = y|，該子集中便有 |(x,y)| 這個元素。例如，|double :: Nat -> Nat| 可表示成如下的集合：
```equation
   \{(0,0), (1,1), (2,4), (3,6), (4,8) \ldots \} \mbox{~~.}
```
能稱為函數的集合還需滿足兩個額外條件：

  * 簡單性(*simplicity*): 對所有 $x \in |A|$, 該集合中僅存在一對唯一的 |(x,y)|。意即每個輸入只對應到一個輸出。
  * 完整性(*totality*): 對所有 $x \in |A|$, 在該集合中都存在某對 |(x,y)|。意即值域中的每個元素都被涵蓋到。


至於遞迴函數呢？以階層 |fact| 為例，其定義為：
```spec
fact :: Nat -> Nat
fact Zero     = 1
fact (Suc n)  = (Suc n) * fact n {-"~~."-}
```
{.nobreak}我們可想成：有一個從集合到集合的函數 |factF|，
```equation
  \Varid{factF}~X ~=~ \{(|Zero|,1)\} \cup \{(|Suc n|, (|Suc n|) \times m) \mid (n,m) \in X \} \mbox{~~.}
```
{.nobreak}給任何集合 |X|，|factF| 傳回這樣的集合：

  * 新集合中有 |(Zero,1)| --- 這對應到 |fact Zero = 1|.
  * 對 |X| 之中的每一個 |(n,m)|, 新集合中有 |(Suc n, (Suc n) * m)| --- 這對應到 |fact (Suc n)  = (Suc n) * fact n|.


{.nobreak}而函數 |fact| 的語意就是 |factF| 唯一的定點 (fixed point).\index{fixed point 定點}
意即 |fact| 是唯一滿足 |fact = factF fact| 的集合。
關於定點的較完整理論可參照第 \@ref{sec:induction-set-theory} 節。
確實，|fact| 可寫成集合如下：
```spec
 fact = {(0,1),(1,1),(2,2),(3,6),(4,24)...} {-"~~."-}
```
{.nobreak}若將 |fact| 餵給 |factF|,
```spec
   factF fact
=  {(0,1)} `union` {(Suc n, (Suc n) * m) | (n,m) `elem` {(0,1),(1,1),(2,2),(3,6)...}}
=  {(0,1)} `union` {(1,1),(2,2),(3,6),(4,24)...} {-"~~,"-}
```
{.nobreak}我們又得到了 |fact|. 因此 |fact| 確實是 |factF| 的定點。

但，要把「|fact| 便是 |factF| 的定點」當作 |fact| 的定義，我們還得確定：確實只有這麼一個集合滿足 |fact = factF fact|。
讀者稍加檢查一下，即可發現確實如此 ---
例如，把 |fact| 添一項或刪一項，都會使得 |factF fact| 不等於 |fact|.

並不是所有從集合到集合的函數都有唯一的定點。考慮如下兩個函數：
::: {.multicols}
::: {.mcol width="0.5\\textwidth"}
```spec
g 0  = 0
g x  = g (Suc x) {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```spec
h 0  = 0
h x  = (-1) * h x {-"~~."-}
```
:::
:::
{.nobreak}若以類似 |fact| 的方式試圖將它們寫成某函數的定點，我們可能寫出如下的 |gF| 和 |hF|:
```spec
gF X  = {(0,0)} `union` {(n,m) | (Suc n,m) `elem` X}  {-"~~,"-}
hF X  = {(n,(-1*m)) | (n,m) `elem` X} {-"~~."-}
```
{.nobreak}但 |gF| 的定點有
```spec
  {(0,0),(1,1),(2,1),(3,1)...} {-"~~,"-}
  {(0,0),(1,2),(2,2),(3,2)...} {-"~~,"-}
  {(0,0),(1,10),(2,10),(3,10)...} {-"~~..."-}
```
{.nobreak}等無限多個。而 |hF| 有一個唯一定點：空集合，但空集合違反了前述的完整性要求。

如同 |g| 和 |f| 這樣的函數，在我們目前介紹的簡單指稱語意中是沒有定義的。
它們沒有語意，在我們的語言中是不該有的存在。
它們剛好也是執行起來不會終止的函數。
因此，我們似乎可以猜測「有唯一定點」和「執行會終止」似乎有些關聯。
但，如前所述，我們的指稱語意中沒有「執行」的觀念。
那是操作語意擅長描述的。

值得一提地，指稱語意採取了一個靜態的世界觀。
一個函數單純地*是*輸入與輸出的對應，沒有「執行」的觀念，沒有執行快慢的考量，也沒有預設「終止」的概念。
```texonly
%{
%format double1
%format double2
```
函數 |double1 x = x + x| 與 |double2 x = 2 * x| 使用不同的演算法，但它們的語意都是同一個集合，因此被視為同一個函數 --- 在語意上我們無法區分 |double1| 與 |double2|。
```texonly
%}
```
在指稱語意中，當我們說兩個函數相等，意指它們的語意是同一個集合。
例如，|map Suc . concat = concat . map (map (Suc))|, 因為兩者的語意都是下述的集合：
```spec
 {([],[]), ... ([[1],[2]], [2,3]),... ([[1],[2,3]],[2,3,4]), ...} {-"~~."-}
```

## 操作語意 {#sec:operational-semantics}

*操作語意*(operational semantics)\index{semantics 語意!operational 操作語意}談一個程式*做什麼*。
在操作語意中，我們通常不談符號的「意思」是什麼。
符號 |Zero| 只代表它本身，|Suc Zero| 也只代表它本身。
操作語意著重的是一串符號如何變成另一段符號。
在這個意義下，前述的 |fact| 定義：
```spec
fact :: Nat -> Nat
fact Zero     = 1
fact (Suc n)  = (Suc n) * fact n {-"~~,"-}
```
{.nobreak}從操作語意的觀點可被讀解成覆寫規則：看到 |fact Zero|, 均可改寫為 |1|; 看到 |fact (Suc n)|, 均可改寫為 |(Suc n) * fact n|.
歸約 |fact (Suc (Suc Zero))| 這個式子可被視為是不斷使用這兩條覆寫規則：
```spec
   fact (Suc (Suc Zero))
=  (Suc (Suc Zero)) * fact (Suc Zero)
=  (Suc (Suc Zero)) * (Suc Zero) * fact Zero
=  (Suc (Suc Zero)) * (Suc Zero) * 1 {-"~~,"-}
```
{.nobreak}其中的每個等號都可讀解為「改寫成」。

操作語意中較容易談「執行」與「終止」的概念。
改寫一個式子相當於執行它，如果已經沒有可改寫之處，也就是碰到了範式，執行便終止了。
在操作語意中，兩個數值（例如 |4+4| 與 |2*4|）相等意謂它們可被歸約成同一個範式；
兩個函數 |f| 和 |g| 相等則意謂對於任何 |x|, |f x| 與 |g x| 都相等。

有了兩種談語意的方式，我們自然希望它們有些一致性。確實，我們有如下的定理：
:::{.theorem #thm:operational-denotational}
操作語意保持指稱語意。意即，給定一個有指稱語意的算式 |e|, 若算式 |e| 能在零步或多步之內依據操作語意改寫成 |e'|, 則 |e| 與 |e'| 的指稱語意相同。
:::

:::{.theorem #thm:semantics-fixedpoint}
給定一個遞迴的函數定義 |f = F f|。若在操作語意中，該函數對所有輸入都正常終止，則在指稱語意中，|f| 是 |F| 的唯一定點。
:::

我們在下一節會
