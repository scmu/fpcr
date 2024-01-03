
``` {.haskell .invisible}
{-# LANGUAGE TypeOperators, StandaloneDeriving #-}
module Chapters.Basics where

import Data.Char (ord, chr)

import Prelude ()
import Common.MiniPrelude hiding (until, gcd)
```

# 值、函數、與定義 {#ch:basics}

語言是概念的載體。
如第\@ref{ch:intro}章所述，程式語言不僅用來表達概念，也用於演算，分擔我們思考的負擔。
在本書中，為便於精確說明，我們也不得不選一個語言。

本書中使用的語言大致上基於 Haskell, 但為適合本書使用而經過簡化、修改。
我們將在本章初步介紹 Haskell 語言的一小部分，包括在 Haskell 中何謂「計算」、值與函數的定義、常見的資料結構，以及串列上的常用函數。
目的是讓讀者具備足夠的基本概念，以便進入之後的章節。
也因此，本書中所介紹的語言並非完整的 Haskell, 本書也不應視作 Haskell 語言的教材。
對於有此需求的讀者，我將在本章結尾推薦一些適合的教科書。

## 值與求值 {#sec:evaluation}

Haskell 是個可被編譯(compile)、也可被直譯(interpret)的語言。Haskell 直譯器延續了 LISP 系列語言的傳統，是個「讀、算、印 (read, evaluate, pring)」的迴圈 --- 電腦從使用者端讀取一個算式，算出結果，把結果印出，然後再等使用者輸入下一個算式。一段與 Haskell 直譯器的對話可能是這樣：
```spec
Main> 3+4
7
Main> sum [1..100]
5050
Main>
```
{.nobreak}在此例中，|Main>| 是 Haskell 直譯器的提示符號。
^[此處的人機互動紀錄擷取自 GHCi (Glasgow Haskell Compiler Interactive). GHC 為目前最被廣泛使用的 Haskell 實作。]
使用者輸入 |3+4|, Haskell 算出其值 |7| 並印出.
接著，使用者想得知 |1| 到 |100| 的和，Haskell 算出 |5050|.

上例中的算式只用到 Haskell 已知的函數（如|(+)|, |sum|等）。
使用者若要自己定義新函數，通常得寫在另一個檔案中，命令 Haskell 直譯器去讀取。
例如，我們可把如下的定義寫在一個檔案中：
```spec
double :: Int -> Int
double x = x + x {-"~~."-}
```
{.nobreak}上述定義的第一行是個型別宣告。當我們寫 |e :: t|, 代表 |e| 具有型別 |t|.
\index{::@@{|(::)|}}
|Int| 是整數的型別，而箭號 |(->)| 為函數型別的建構元。第一行 |double :: Int -> Int| 便是告知電腦我們將定義一個新識別字 |double|, 其型別為「從整數(|Int|)到整數的函數」。
^[Haskell 標準中有多種整數，其中 |Int| 為有限大小（通常為該電腦中一個*字組*(word)）的整數，|Integer| 則是所謂的*大整數*或*任意精度整數*，無大小限制。本書中只使用 |Int|.]
至於該函數的定義本體則在第二行 |double x = x + x|, 告知電腦「凡看到 |double x|, 均可代換成 |x + x|.」

{title="求值"}第\@ref{ch:intro}章曾提及：一套程式語言是設計者看待世界的抽象觀點。程式通常用來表達計算，因此程式語言也得告訴我們：在其假想的世界中，「計算」是怎麼一回事。
指令式語言的世界由許多容器般的變數組成，計算是將值在變數之間搬來搬去。
邏輯編程\index{logic programming 邏輯編程}中，描述一個問題便是寫下事物間的邏輯關係，計算是邏輯規則「歸結(resolution)」\index{logic programming 邏輯編程!resolution 歸結}的附帶效果。
共時(concurrent)\index{concurrency 共時}程式語言著眼於描述多個同時執行的程式如何透過通道傳遞訊息，計算也靠此達成。
::: {.infobox title="演算格式"}
::: {.texonly}
```
%format expr0
%format expr1
%format expr2
%format exprn = "\Varid{expr}_{n}"
%format reason0
%format reason1
```
:::
本書中將使用如下的格式表達（不）等式演算或推論：
``` spec
   expr0
 =   { reason0 }
   expr1
 >=  { reason1 }
   expr2
   :
 = exprn {-"~~."-}
```
這是一個 |expr0 >= exprn| 的證明。式子 |expr0 .. exprn| 用具有遞移律的運算子(如|(=)|, |(>=)|等等)串起。放在大括號中的是註解，例如 |reason0| 是 |expr0 = expr1| 的原因，|reason1| 是 |expr1 >= expr2| 的原因。

根據 @Snepscheut:93:What[p19], 此格式最早由 W.H.J. Feijen 所建議。
:::

函數語言中，一個程式便是一個數學式，而「計算」便是依照該式子中各個符號的定義，反覆地展開、歸約，直到算出一個「值」為止。
這個過程又稱作「求值(evaluation)」\index{evaluation 求值}。
在 Haskell 直譯器中，若 |double| 的定義已被讀取，輸入 |double (9 * 3)|, 電腦會算出 |54|:
```spec
Main> double (9 * 3)
54
```
但 |54| 這個值是怎麼被算出來的？以下是其中一種可能：
```spec
  double (9 * 3)
=   {- |(*)| 的定義 -}
  double 27
=   {- |double| 的定義 -}
  27 + 27
=   {- |(+)| 的定義 -}
  54 {-"~~."-}
```
{.nobreak}上述演算的第一步將 |9*3| 歸約成 |27| --- 我們尚未定義 |(*)| 與 |(+)|, 但目前只需知道它們與大家所熟悉的整數乘法、加法相同。
第二步將 |double 27| 變成 |27 + 27|, 根據的是 |double| 的定義：|double x = x + x|.
最後，|27 + 27| 理所當然地歸約成 |54|.
「歸約」\index{reduction 歸約}一詞由 $\beta$-reduction 而來，在此處指將函數本體中的形式參數代換為實際參數。%
^[Reduction 的另一個常見譯名是「化簡」，然而，許多情況下，一個式子被 reduce 後變得更長而不「簡」，因此本書譯為「歸約」。]
在上述例子中，我們遇到如 |double (9*3)| 的函數呼叫，先將參數 (|9*3|)化簡，再展開函數定義，可說是*由內到外*的歸約方式。
大部分程式語言都依這樣的順序求值，讀者可能也對這種順序較熟悉。

但這並不是唯一的求值順序。我們能否由外到內，先把 |double| 展開呢？
```spec
  double (9 * 3)
=   {- |double| 的定義 -}
  (9 * 3) + (9 * 3)
=   {- |(*)| 的定義 -}
  27 + (9 * 3)
=   {- |(*)| 的定義 -}
  27 + 27
=   {- |(+)| 的定義 -}
  54 {-"~~."-}
```
{.nobreak}以這個順序求值，同樣得到 |54|.

一般說來，一個式子有許多種可能的求值順序：可能是由內往外、由外往內、或其他更複雜的順序。
我們自然想到一個問題：這些不同的順序都會把該式子化簡成同一個值嗎？
有沒有可能做出一個式子，使用一個順序會被化簡成 |54|, 另一個順序化簡成 |53|?

我們看看如下的例子。
函數 |three| 顧名思義，不論得到什麼參數，都傳回 |3|；|inf| 則是一個整數：
```spec
three :: Int -> Int
three x = 3 {-"~~,"-}

inf :: Int
inf = 1 + inf {-"~~."-}
```
{.nobreak}在指令式語言中，|inf| 的定義可能會被讀解為「將變數 |inf| 的值加一」。
但函數語言中「變數」的值是不能更改的。
此處的意義應是：|inf| 是一個和 |1 + inf| 相等的數值。
我們來看看 |three inf| 會被為甚麼？
如果我們由內往外求值：
```spec
  three inf
=   {- |inf| 的定義 -}
  three (1 + inf)
=   {- |inf| 的定義 -}
  three (1 + (1 + inf))
=   {- |inf| 的定義 -}
  ...
```
{.nobreak}看來永遠停不下來！但如果我們由外往內，|three inf| 第一步就可變成 |3|：
```spec
  three inf
=   {- |three| 的定義 -}
  3 {-"~~."-}
```
{.nobreak}我們該如何理解、討論這樣的現象呢？

{title="範式與求值順序"}
為描述、討論相關的現象，我們得非正式地介紹一些術語。
用較直觀、不形式化的方式理解，一個式子中「接下來可歸約之處」稱作其*歸約點(redex)*\index{redex 歸約點}。例如|(9*3) + (4*6)|中，|9*3| 與 |4*6| 都是歸約點。
如果一個式子已沒有歸約點、無法再歸約了，我們說該式已是個*範式 (normal form)*\index{normal form 範式}。

回頭看，經由之前的例子我們已得知：

  * 有些式子有範式(如 |double (9*3)| 有個範式 |54|)，有些沒有（如 |inf|）。
  * 同一個式子可用許多順序求值。有些求值順序會碰到範式，有些不會。

{.nobreak}給一個式子，我們很自然地希望知道它有沒有值，並算出其值。如果一個式子有很多個範式，我們便難說哪一個才是該式子的「值」。如此一來，立刻衍生出幾個問題。給定一個式子，我們是否能得知它有沒有範式呢？如果有，用哪個求值順序才能得到那個範式？以及，有沒有可能用一個求值順序會得到某範式，換另一個求值順序卻得到另一個範式？

很不幸地，第一個問題的答案是否定的：沒有一套固定的演算法可判定任意一個式子是否有範式。
這相當於計算理論中常說到的*停機問題(halting problem)* --- 沒有一個演算法能準確判斷任意一個演算法（對某個輸入）是否能正常終止。

但對於另兩個問題，計算科學中有個重要的*Church-Rosser 定理*\index{Church-Rosser Theorem}。
非常粗略地說，該定理告訴我們：在我們目前討論的這類語言中%
^[此處討論的可粗略說是以 $\lambda$-calculus 為基礎的函數語言。基於其他概念設計的程式語言當然可能不遵守 Church-Rosser 定理。]

  * 一個式子*最多只有一個*範式。
  * 如果一個式子有範式，使用由外到內的求值順序可得到該範式。

{.nobreak}如此一來，給定任一個式子，我們都可用由外到內的方式算算看。
假設一算之下得到（例如）|54|。
用其他的求值順序可能得不到範式，但若有了範式，必定也是 |54|.
如果由外到內的順序得不到範式，用其他任何順序也得不到。

由於「由外到內」的求值順序有「最能保證得到範式」的性質，又被稱作「*範式順序* (*normal order evaluation*)」\index {evaluation 求值!normal order 範式順序}。
「由內到外」的則被稱作「*應用順序*(*applicative order evaluation*)」\index {evaluation 求值!applicative order 應用順序}。
以本書的目的而言，我們可大致把 Haskell 使用的求值方式視為範式順序。
但請讀者記得這是個粗略、不盡然正確的說法 --- Haskell 實作上使用的求值方式經過了更多最佳化。
正式的 $\lambda$-calculus 教科書中對於歸約點、求值順序、Church-Rosser 定理等概念會有更精確的定義。

{title="被迫求值"}
型別 |Bool| 表示真假，有兩個值 |False| 和 |True|。
常用的函數 |not| 可定義如下：
```spec
not :: Bool -> Bool
not False  = True
not True   = False {-"~~."-}
```
{.nobreak}此處 |not| 的定義依輸入值不同而寫成兩個條款。
這種定義方式在 Haskell 中稱作*樣式配對*(*pattern matching*)：
|False| 與 |True| 在此處都是樣式 (patterns)。\index{pattern matching 樣式配對}
遇到這樣的定義時，Haskell 將輸入*依照順序*與樣式們一個個比對。
如果對得上，便傳回相對應的右手邊。
本例中，若輸入為 |False|，傳回值為 |True|，否則傳回值為 |False|。

我們來看看 |not (5 <= 3)| 該怎麼求值？若依照範式順序，照理來說應先將 |not| 的定義展開。
但若不知 |5 <= 3| 的值究竟是 |False| 還是 |True|, 我們不知該展開哪行定義！
因此，要計算 |not (5 <= 3)|，也只好先算出 |5 <=3| 了：
```spec
  not (5 <= 3)
=   {- |(<=)| 之定義 -}
  not False
=   {- |not| 之定義 -}
  True {-"~~."-}
```

求值過程中若必須得知某子算式的值才能決定如何進行，只好先算那個子算式。
在 Haskell 中有不少（有清楚定義的）場合得如此，
包括遇上|(<=)|、|(>=)| 等運算子、樣式配對、|case| 算式（將於第\@ref{sec:boolean}節中介紹）...等等。

::: {.exlist}
::: {.exer #ex:myeven}
定義一個函數 |myeven :: Int -> Bool|，判斷其輸入是否為偶數。
你可能用得到以下函數：^[此處所給的並非這些函數最一般的型別。]
```spec
mod   :: Int -> Int -> Int {-"~~,"-}
(==)  :: Int -> Int -> Bool {-"~~."-}
```
其中 |mod x y| 為 |x| 除以 |y| 之餘數，|(==)| 則用於判斷兩數是否相等。
:::
::: {.exans .compact}
```spec
myeven   :: Int -> Bool
myeven x = x `mod` 2 == 0  {-"~~."-}
```
:::
::: {.exer #ex:circle-area}
定義一個函數 |area :: Float -> Float|, 給定一個圓的半徑，
計算其面積。（可粗略地將 |22/7| 當作圓周率。）
:::
::: {.exans .compact}
```spec
area    :: Float -> Float
area r  = (22/7) * r * r {-"~~."-}
```
:::
:::

{title="惰性求值" #para:lazy-evaluation}
\index{evaluation 求值!lazy evaluation 惰性求值}
實作上，Haskell 求值的方式還經過了更多的最佳化：
例如將歸約過的算式改寫為它的值，避免重複計算。
這套求值方式稱為*惰性求值*(*lazy evaluation*).

技術上說來，惰性求值和範式順序求值並不一樣。
但前者可視為後者的最佳化實作 --- 惰性求值的結果必須和範式順序求值相同。
因此，在本書之中大部分地方可忽略他們的差異。
和惰性求值對偶的是*及早求值*(*eager evaluation*)
\index{evaluation 求值!eager evaluation 及早求值}，
可視為應用順序求值的實作 --- 在呼叫一個函數之前，總是把其參數先算成範式。
這也是一般程式語言較常見的計算方法。

本書中談到偏向實作面的議題時會用「惰性求值/及早求值」，
在談不牽涉到特定實作的理論時則使用「範式順序求值/應用順序求值」。

## 函數定義 {#sec:function-defns}

考慮如下的函數定義：
```spec
smaller :: Int -> Int -> Int
smaller x y = if x <= y then x else y {-"~~."-}
```
我們可粗略地理解為：|smaller| 是一個函數，拿兩個參數 |x| 與 |y|，傳回其中較小的那個。
如 |smaller (double 6) (3+4)| 的值為 |7|.

::: {.exlist}
::: {.exer #ex:smaller-normal-form}
用前一節介紹的求值順序，將|smaller (double 6) (3+4)|化簡為範式。
:::
:::

{title="守衛"} 如果函數本體做的第一件事就是條件判斷，Haskell 提供另一種語法：
```spec
smaller :: Int -> Int -> Int
smaller x y  | x <= y  = x
             | x > y   = y {-"~~."-}
```
{.nobreak}這麼寫出的 |smaller| 的行為仍相同：如果 |x <= y| 成立，傳回 |x|；如果 |x > y|, 傳回 |y|。
但這種語法較接近一些數學教科書中定義函數的寫法。
其中，放在 |x <=y| 和 |x > y| 等位置的必須是型別為 |Bool| 的算式。
它們擋在那兒，只在值為 |True| 的時候才讓執行「通過」，因此被稱為*守衛*(*guard*)\index{guard 守衛}。
如果有三個以上的選項，如下述例子，使用守衛比 |if .. then.. else| 更清晰可讀：
```spec
sign :: Int -> Int
sign x  | x > 0   = 1
        | x == 0  = 0
        | x < 0   = -1 {-"~~."-}
```

遇到數個守衛時，Haskell 將*依照順序*嘗試每個選項，直到碰到第一個為真的守衛，然後只執行該項定義。
也就是說， 即使我們把 |sign| 定義中的 |x == 0| 改為 |x >= 0|, |sign 10| 的值仍會是 |1|。
若每個守衛都是 |False|, 程式則將中斷執行（並傳回一個錯誤訊息）。
在許多程式中，我們會希望最後一個守衛能捕捉所有的漏網之魚：如果其他條款都不適用，就執行最後一個。一種做法是讓一個守衛是 |True|。或著，在 Haskell 中有個 |otherwise| 關鍵字可讓定義讀來更口語化些：
```spec
sign :: Int -> Int
sign x  | x > 0      = 1
        | x == 0     = 0
        | otherwise  = -1 {-"~~."-}
```
事實上，|otherwise| 的定義就是 |otherwise = True|.

{title="區域識別字"} Haskell 提供兩種宣告區域識別字的語法：|let| 與 |where|.
也許最容易理解的方式是用例子說明。
::: {.example #eg:payment}
工讀生每小時的時薪為新台幣 130 元。
假設一週有五個工作天，每天有八小時上班時間。
定義一個函數 |payment :: Int -> Int|，輸入某學生工作的週數，計算其薪資。
:::
::: {.answer}
我們當然可直接用一個式子算出薪資。但為清楚起見，我們可用兩個區域識別字 |days| 和 |hours|,
分別計算該學生工作的日數和時數。如果用 |let|, 可這麼做。
```spec
payment :: Int -> Int
payment weeks =  let  days   = 5 * weeks
                      hours  = 8 * days
                 in 130 * hours {-"~~."-}
```
{.nobreak}|let| 算式的語法為
```spec
  let  x1 = e1
       x2 = e2 ....
  in e {-"~~."-}
```
{.nobreak}其中 |e| 為整個算式的值，而 |x1|, |x2| 等等為區域識別字。兩個區域識別字的有效範圍包括 |e|, 以及 |e1| 與 |e2|。

另一種語法是 |where| 子句。若用它定義 |payment|, 可寫成這樣：
```spec
payment :: Int -> Int
payment weeks = 130 * hours {-"~~,"-}
  where  hours  = 8 * days
         days   = 5 * weeks {-"~~."-}
```
:::

該用 |let| 或是 |where|?
大部份時候這可依個人習慣，看寫程式的人覺得怎麼說一件事情比較順。
使用 |let| 時，敘事的順序是由小到大，先給「工作日數」、「工作時數」等小元件的定義，再用他們組出最後的式子 |130 * hours|。
使用 |where| 時則是由大到小，先說我們要算「工作時數乘以 130」，然後補充「其中，工作時數的定義是...」。

但，Haskell 之所以保留了兩種語法，是為了因應不同的用途。語法上，|let| 是一個算式，可出現在算式中。如下的算式是合法的，其值為 |24|:
```spec
   (1 + 1) * (let y = double 5 in y + 2) {-"~~."-}
```
{.nobreak}|where| 子句的一般語法則如下例所示：
```spec
f x0 = d0
   where y0 = e0
f x1 = d1
   where y1 = e1 {-"~~."-}
```
{.nobreak}由語法設計上即可看出，子句 |where y0 = e0| 只能放在 |f x0 = ...| 的一旁當作補述，不能出現在 |d0| 之中。
這個例子中， |y0| 的有效範圍含括 |d0| 與 |e0|。另，|e0| 可以使用 |x0|.

算式中只能用 |let|. 相對地，也有些只能使用 |where| 的場合。我們來看
我們來看一個只能使用 |where| 的例子：
::: {.example #eg:payment2}
延續例 \@ref{eg:payment}。
今年起，新勞動法規規定工作超過 19 週的工讀生必須視為正式雇員，
學校除了薪資外，也必須付給勞保、健保費用。
學校需負擔的勞健保金額為雇員薪資的百分之六。請更新函數 |payment|,
輸入某工讀生工作週數，計算在新規定之下，學校需為工讀生付出的總額。
:::
::: {.answer}
一種可能寫法是先使用守衛，判斷工作週數是否大於 19：
```spec
payment :: Int -> Int
payment weeks  | weeks > 19  = round (fromIntegral baseSalary * 1.06)
               | otherwise   = baseSalary {-"~~,"-}
 where  baseSalary = 130 * hours
        hours  = 8 * days
        days   = 5 * weeks {-"~~."-}
```
{.nobreak}在 |where| 子句中，我們先算出不含勞健保費用的薪資，用識別字 |baseSalary| 表達。
如果 |weeks| 大於 |19|, 我們得將 |baseSalary| 乘以 |1.06|；否則即傳回 |baseSalary|.
函數 |fromIntegral| 把整數轉為浮點數，|round| 則把浮點數四捨五入為整數。
請注意：兩個被守衛的算式都用到了 |baseSalary| ---
|where| 子句中定義的識別字是可以跨越守衛的。
相較之下，|let| 算式只能出現在等號的右邊，而在守衛 |weeks > 19 = ...| 之後出現的
|let| 所定義出的區域識別字，顯然無法在 |otherwise = ...| 之中被使用，反之亦然。
:::

{title="巢狀定義"} |let| 算式之中還可有 |let| 算式，
|where| 子句中定義的識別字也可有自己的 |where| 子句。
我們看看兩個關於 |let| 的例子：
::: {.example #eg:nested-recursive}
猜猜看 |nested| 和 |recursive| 的值分別是什麼。
將他們載入 Haskell 直譯器，看看和你的猜測是否相同。
::: {.multicols}
::: {.mcol width="0.4\\textwidth"}
```spec
nested :: Int
nested =  let x = 3
          in (  let  x = 5
                in x + x) + x {-"~~,"-}
```
:::
::: {.mcol width="0.4\\textwidth"}
```spec
recursive :: Int
recursive =  let x = 3
             in  let x = x + 1
                 in x {-"~~."-}
```
:::
:::
::: {.answer}
|nested| 的值是 |13|，因為 |x+x| 之中的 |x| 在 |let x = 5| 的範圍中,
而 |.. + x| 中的 |x| 則在 |let x = 3| 的範圍中。^[在各種語言中，範圍的設計都是為了給程式員方便：在寫子算式時，可不用擔心是否與外層的識別字撞名。在教學時，我們難免舉各種撞名的例子作為說明。若把這些刁鑽例子當作考題，就是違反設計者本意的發展了。]
至於 |recursive| 的值，關鍵在於 |x = x + 1| 中右手邊的 |x| 指的是哪個。
若是 |x = 3| 的那個 |x|, 整個算式的值將是 |4|. 若 |x = x + 1| 中，
等號右手邊的 |x| 也是左手邊的 |x|, |recursive| 就是 |((..)+1)+1| , 沒有範式。
這兩種設計都有其道理。
Haskell 選了後者：在 |let x = e in ...| 之中，|x| 的有效範圍包括 |e|.
因此 |recursive| 在 Haskell 中會無窮地求值下去。
但也有些函數語言中的 |let| 採用前者的設計。通常這類語言中會另有一個 $\Keyword{letrec}$
結構，和 Haskell 的 |let| 功能相同。
:::
:::

## 高階函數 {#sec:higher-order-func}

目前為止，我們看過由整數到整數的函數、由整數到真假值的函數...
那麼，可以有由函數到函數的函數嗎？
函數語言將函數視為重要的構成元件，因此函數也被視為*一級公民*。
如果整數、真假值... 可以當作參數、可以被函數傳回，函數當然也可以。
一個「輸入或輸出也是函數」的函數被稱為*高階函數*(*higher order function*)\index{higher-order function 高階函數}。
Haskell 甚至設計了許多鼓勵我們使用高階函數的機制。
本書中我們將見到許多高階函數。其實，我們已經看過一個例子了。

::: {.infobox title="一級公民"}
在程式語言中，若說某物/某概念是*一級公民*(*first-class citizen*)\index{first-class citizen 一級公民}或「一級的」，
通常指它和其他事物被同等對待：
如果其他事物可被當作參數、可被當作傳回值、可被覆寫...那麼它也可以。
這是一個沒有嚴格形式定義的說法，由 Christopher Strachey 在 1960 年代提出，
可用在型別、值、物件、模組... 等等之上。

例如：OCaml 是個有「一級模組」的語言，因為 OCaml 模組也可當作參數，可定義從模組到模組的函數（OCaml 中稱之為 functor）。
在 C 語言之中函數是次級的，因為函數不能當參數傳（能傳的是函數的指標，而非函數本身）。
Strachey指出，在 Algol 中實數是一級的，而程序是次級的。
:::

{title="Currying"} 回顧|smaller|的定義：
```
smaller :: Int -> Int -> Int
smaller x y = if x <= y then x else y {-"~~."-}
```
\@ref{sec:function-defns} 節中說「|smaller| 是一個函數，拿兩個參數 |x| 與 |y|」。
但這僅是口語上方便的說法。
事實上，在 Haskell 中（如同在 $\lambda$-calculus 中），所有函數都只有一個參數。
函數 |smaller| 其實是一個\emph{傳回函數的函數}：

  *  |smaller| 的型別 |Int -> Int -> Int| 其實應看成 |Int -> (Int -> Int)|：
這個函數拿到一個 |Int| 後，會傳回一個型別為 |Int -> Int| 的函數。
  * |smaller 3| 的型別是 |Int -> Int|。這個函數還可拿一個 |Int| 參數，將之和 |3| 比大小，傳回較小的那個。
  * |smaller 3 4| 是一個 |Int|。它其實是將函數 |smaller 3| 作用在 |4| 之上。也就是說，|smaller 3 4| 其實應看成 |(smaller 3) 4|. 根據定義，它可展開為 |if 3 <= 4 then 3 else 4|，然後化簡為 |3|.

::: {.exlist}
::: {.exer #ex:smaller-inpt}
將 |smaller| 的定義鍵入一個檔案，載入 Haskell 直譯器中。

  1. |smaller 3 4| 的型別是什麼？在 GHCi 中可用 {\tt :t e} 指令得到算式 |e| 的型別。
  2. |smaller 3| 的型別是什麼？
  3. 在檔案中定義 |st3 = smaller 3|. 函數 |st3| 的型別是什麼？
  4. 給 |st3| 一些參數，觀察其行為。


:::
:::

「用『傳回函數的函數』模擬『接收多個參數的函數』」這種做法稱作 *currying*.
\index{currying}^[Currying 為動名詞，形容詞則為 *curried*。
此詞來自於邏輯學家 Haskell B. Curry 的姓氏。
詳見第 \@ref{sec:refs-basics} 節。]
Haskell 鼓勵大家使用 currying --- 它的內建函數大多依此配合設計，
語法設計上也很給 currying 方便。
當型別中出現連續的 |(->)| 時，預設為往右邊結合，例如
|Int -> Int -> Int| 應看成 |Int -> (Int -> Int)|.
這使得「傳回函數的函數」容易寫。
而在值的層次，連續的函數應用往左結合。
例如，|(smaller 3) 4| 可寫成 |smaller 3 4|。
這讓我們能很方便地將參數一個個餵給 curried 函數。

另一方面，如果我們想使用 |double| 兩次，計算 |x| 的四倍，應寫成 |double (double x)|.
若寫 |double double x| ，會被視為 |(double double) x| --- |double| 作用在自身之上，而這顯然是個型別錯誤。
::: {.texonly}
```
%format poly1
%format poly2
```
:::


我們再看一個使用 currying 的練習：
::: {.example #eg:polynomial}
給定 |a|, |b|, |c|, |x|, 下述函數 |poly| 計算 $ax^2 + bx + c$:
```spec
poly :: Int -> Int -> Int -> Int -> Int
poly a b c x = a * x * x + b * x + c {-"~~."-}
```
請定義一個函數 |poly1|, 使得 $poly_1~x = x^2 + 2x + 1$.
函數 |poly1| 需使用 |poly|.
:::
::: {.answer}
一種作法是：
```spec
poly1 :: Int -> Int
poly1 x = poly 1 2 1 x {-"~~."-}
```
但這相當於 |poly1 x = (poly 1 2 1) x| ---
|poly| 拿到 |x| 後，立刻把 |x| 傳給 |poly 1 2 1| 這個函數。
因此 |poly1| 可更精簡地寫成：
```spec
poly1 :: Int -> Int
poly1 = poly 1 2 1 {-"~~."-}
```
{.nobreak}兩種寫法都有人使用。
有提及|x|的寫法著重於描述拿到參數|x|之後要對它進行什麼操作。
而省略|x|的寫法則是在函數的層次上思考：
我們要定義一個函數，稱作|poly1|。這個函數是什麼呢？
*就是 |poly| 拿到 |1|, |2|, |1| 之後傳回的那個函數。*

如果我們想用 |poly| 定義出另一個函數
$poly_2~a~b~c = a\times 2^2 + b \times 2 + 2$ 呢？
最好理解的可能是不怎麼意外的寫法：
```spec
poly :: Int -> Int -> Int -> Int
poly2 a b c = poly a b c 2 {-"~~."-}
```
我們可以用一些技巧使 |a|, |b|, 和|c|不出現在定義中，
但如此得到的程式並不會更好懂。
:::

{title="二元運算子"}
在進入其他主題前，我們交代一些語法細節。
Haskell 鼓勵 currying 的使用，也把二元運算子都設計成 curried 的。
例如加法的型別是 |Int -> Int -> Int|.
Haskell 也配套設計了種種關於二元運算子的特殊語法，希望讓它們更好用。
但這些語法規則的存在都僅是為了方便我們寫出（主觀上）語法漂亮的程式，
而不是非有不可、非學不可的規定。

{#par:binary-operator-sectioning}
假設某二元運算子 |oplus| 的型別是 |a -> b -> c|,
|(x `oplus`)| 是給定了 |oplus| 的第一個參數後得到的函數；
|(`oplus` y)| 則是給定了 |oplus| 的第二個參數後得到的函數：%
^[根據@Hudak:07:Being，此種「*切片*」(*sectioning*)語法最早見於 David Wile 的博士論文。
後來被包括 Richard Bird 在內的 IFIP WG 2.1 成員使用，並由 David A. Turner 實作在他的語言 Miranda 中。]
```spec
(x `oplus`) y  = x `oplus` y  {-"\quad"-}  {- |(x `oplus`)| 的型別為 |b -> c|; -}
(`oplus` y) x  = x `oplus` y               {- |(`oplus` y)| 的型別為 |a -> c|.-}
```
{.nobreak}例如：

  * |(2 *)| 和 |(* 2)| 都是把一個數字乘以二的函數；
  * |(/ 2)| 則把輸入數字除以二；
  * |(1 /)| 計算輸入數字的倒數。

名字以英文字母開頭的函數預設為前序的。例如，
計算餘數的函數 |mod| 使用時得寫成 |mod 6 4|。
若把它放在「倒引號(backquote)」中，表示將其轉為中序 ---
如果我們比較喜歡把 |mod| 放到中間，可以寫成 |6 `mod` 4|.
首字元非英文字母的函數（如 |(+)|, |(/)| 等）則會被預設為中序的二元運算子。
若把一個中序二元運算子放在括號中，表示將其轉為前序運算子。
例如，|(+) 1 2| 和 |1 + 2| 的意思相同。

在 Haskell 的設計中，函數應用的優先順序比中序運算子高。
因此 |double 3 + 4| 會被視作 |(double 3) + 4|, 而不是 |double (3+4)|.
將中序運算子放在括號中也有「讓它不再是個中序運算子，只是個一般識別字」的意思。
例如算式 |f + x| 中，|f| 和 |x| 是中序運算子 |(+)| 的參數。
但在 |f (+) x| 中，|(+)| 和 |x| 都是 |f| 的參數
（這個式子可以讀解為 |(f (+)) x|）。

{title="以函數為參數"} 下述函數 |square| 計算輸入的平方：
```haskell
square :: Int -> Int
square x = x * x {-"~~."-}
```
{.nobreak}我們可另定義一個函數 |quad :: Int -> Int|，把 |square| 用兩次，
使得 |quad x| 算出 $x^4$.
```haskell
quad :: Int -> Int
quad x = square (square x)   {-"~~."-}
```

但，「把某函數用兩次」是個常見的編程模式。
我們能不能把 |quad| 與 |square| 抽象掉，單獨談「用兩次」這件事呢？
下面的函數 |twice| 把參數 |f| 在 |x| 之上用兩次：
```haskell
twice      :: (a -> a) -> (a -> a)
twice f x  = f (f x) {-"~~."-}
```
{.nobreak}有了 |twice|, 我們可以這麼定義 |quad|:
```spec
quad :: Int -> Int
quad = twice square {-"~~."-}
```

函數 |twice| 是本書中第一個「以函數為參數」的函數。
我們可看到「讓函數可作為參數」對於抽象化是有益的：
我們可以把「做兩次」這件事單獨拿出來說，把「做什麼」抽象掉。

「函數可以當作參數」意味著我們可以定義*作用在函數上的運算子*。
|twice| 就是這麼一個運算子：
它拿一個函數 |f|，把它加工一下，做出另一個函數（後者的定義是把 |f| 用兩次）。

{title="參數式多型"}
函數 |twice| 也是本書中第一個*多型*函數。
在 Haskell 的型別中，小寫開頭的識別字（如其中的 |a|）是型別層次的參數。
讀者可想像成在 |twice| 的型別最外層有一個省略掉的 |forall a|.
也就是說, |twice| 的完整型別是 |forall a . (a -> a) -> (a -> a)|  ---
對所有的型別 |a|, |twice| 都可拿一個型別為 |a -> a| 的函數，
然後傳回一個型別為 |a -> a| 的函數。

在 |twice| 的型別 |(a -> a) -> (a -> a)| 中，

  * 第一個 |a -> a| 是參數 |f| 的型別，
  * 在第二個 |a -> a| 中，第一個 |a| 是 參數 |x| 的型別，
  * 第二個 |a| 則是整個計算結果的型別。

{.nobreak}參數 |f| 的型別必須是 |a -> a|: 輸出入型別必須一樣，因為 |f| 的結果必須可當作 |f| 自己的輸入。

在 |twice| 被使用時，型別參數 |a| 會依照上下文被*特化*(*instantiate*)成別的型別。
例如 |twice square| 中， 因為 |square| 的型別是 |Int -> Int|,
*這一個* |twice| 的型別變成了 |(Int -> Int) -> (Int -> Int)| --- |a| 被特化成 |Int|.
若某函數 |k| 的型別是 |Float -> Float|, 在 |twice k| 中，|twice| 的型別是 |(Float -> Float) -> (Float -> Float)|。
同一個函數 |twice| 可能依其上下文而有許多不同的型別，但都是 |(a -> a) -> (a -> a)| 的特例。
「一段程式可能有許多不同型別」的現象稱作*多型*(*polymorphism*)\index{polymorphism 多型}。
多型又有許多種類，此處為其中一種。詳情見... \todo{}


::: {.exlist}
::: {.exer #ex:twice-type}
為何 |twice| 的型別不可以是 |(a -> b) -> (a -> b)|?
:::
:::

::: {.example #eg:forktimes}
```haskell
forktimes f g x = f x * g x {-"~~."-}
```
算式 |forktimes f g x| 把 |f x| 和 |g x| 的結果乘起來。

  1. 請想想 |forktimes| 的型別該是什麼？
  2. 試定義函數 |compute :: Int -> Int|, 使用 |forktimes| 計算 $x^2 + 3\times x  + 2$。 **提示**：$x^2 + 3\times x  + 2 = (x+1) \times (x+2)$.


:::
::: {.answer}
如同 |twice|, |forktimes| 可以有很多型別，但都應該是
|(a -> Int) -> (a -> Int) -> a -> Int| 的特例：
在 |forktimes f g x| 中， |f| 和 |g| 的型別可以是 |a -> Int|,
其中 |a| 可以是任何型別 |a|，而 |x| 的型別必須也是同一個 |a|.
函數 |compute| 可定義如下：
```haskell
compute :: Int -> Int
compute = forktimes (+1) (+2) {-"~~."-}
```
其中 |forktimes| 型別中的 |a| 被特化為 |Int|.
:::

::: {.texonly}
```
%format lift2
```
:::

如前所述，|forktimes f g x| 把 |f x| 和 |g x| 的結果乘起來。
但，一定得是乘法嗎？我們當然可以再多做一點點抽象化。
::: {.example #eg:lift2}
考慮函數 |lift2 h f g x = h (f x) (g x)|.

  1. |lift2| 的型別是什麼？
  2. 用 |lift2| 定義 |forktimes|.
  3. 用 |lift2| 計算 $x^2 + 3\times x  + 2$.


:::
::: {.answer}
我們把 |lift2| 最泛用的型別和其定義重複如下：
```haskell
lift2 :: (a -> b -> c) -> (d -> a) -> (d -> b) -> d -> c {-"~~."-}
lift2 h f g x = h (f x) (g x) {-"~~."-}
```
{.nobreak}有了 |lift2|, |forktimes| 可定義為：
```spec
forktimes :: (a -> Int) -> (a -> Int) -> a -> Int
forktimes = lift2 (*) {-"~~,"-}
```
{.nobreak}請讀者觀察：|lift| 型別中的 |a|, |b|, |c| 都特化成 |Int|,
|d| 則改名為 |a|.

我們也可用 |lift2| 定義 |compute|:
```spec
compute :: Int -> Int
compute = lift2 (*) (+1) (+2) {-"~~."-}
```

函數 |lift2| 可以看作一個作用在二元運算子上的運算子，功用是把
二元運算子「提升」到函數層次。
例如，原本 |(*)| 只能拿兩個 |Int| 當作參數，
（例：|1 * 2| 是「把 |1| 和 |2| 乘起來」），
但現在 |lift2 (*)| 可將函數 |(+1)| 和 |(+2)| 當參數了，
意思為「把 |(+1)| 和 |(+2)| 的結果乘起來」。
:::


## 函數合成 {#sec:func-comp}

拿到一個函數 |f|，我們能做的基本操作包括把 |f| 作用在某個參數上、
把 |f| 傳給別的函數...
此外，另一個常用的基本操作是將 |f| 和別的函數*合成*(*compose*)
\index{function composition 函數合成}\index{.@@{|(.)|}}
為一個新函數。
^[Robert Gl\"{u}ck 認為函數上應有三個基本操作：
函數應用、函數合成、以及求一個函數的反函數。
前兩者已經提到，第三者則是大部分語言欠缺的。]
「合成」運算子在 Haskell 中寫成|(.)|.
這個運算子的形式定義如下（我們先看定義本體，待會兒再看型別）：
```spec
(f . g) x  = f (g x) {-"~~."-}
```
若用口語說，|f . g| 是將 |f| 和 |g|兩個函數「串起來」得到的新函數：
輸入 |x| 先丟給 |g|, 後者算出的結果再傳給 |f|.

::: {.example #eg:square-double}
|square . double| 與 |double . square| 都是由 |Int| 到 |Int| 的函數.
直覺上，前者把輸入先給 |double|, 其結果再給 |square|。
後者則反過來。
如何了解它們的行為？既然它們是函數，我們便餵給它們一個參數，看看會展開成什麼！
兩者分別展開如下：
::: {.multicols}
::: {.mcol width="0.4\\textwidth"}
```spec
   (square . double) x
=    {- |(.)| 的定義 -}
   square (double x)
=  (x + x) * (x + x) {-"~~,"-}
```
:::
::: {.mcol width="0.4\\textwidth"}
```spec
   (double . square) x
=    {- |(.)| 的定義 -}
   double (square x)
=  (x * x) + (x * x) {-"~~."-}
```
:::
:::
所以，如果輸入為 |x|, |(square . double) x| 計算 $(2x)^2$;
|(double . square) x| 則是 $2x^2$.
:::

但，並不是所有函數都可以串在一起：
|f . g| 之中，|g| 的輸出型別和 |f| 的輸入型別必須一致才行。
運算子 |(.)| 包括型別的完整定義為：
```spec
(.) :: (b -> c) -> (a -> b) -> a -> c
(f . g) x  = f (g x) {-"~~."-}
```
{.nobreak}如果 |g| 的型別是 |a -> b|, |f| 的型別是 |b -> c|, 將他們串接起來後，
便得到一個型別為 |a -> c| 的函數。

有了|(.)|, 函數 |twice| 可以定義如下：
```spec
twice    :: (a -> a) -> (a -> a)
twice f  = f . f  {-"~~."-}
```
{.nobreak}確實，根據 |(.)| 的定義，|twice f x = (f . f) x = f (f x)|，和 |twice| 原來的定義相同。

為了討論函數合成的性質，我們先介紹一個函數 |id|:
```
id :: a -> a
id x = x {-"~~."-}
```
{.nobreak}它又稱作*單位函數*或*恆等函數*。\index{identity function 單位函數 恆等函數}
這是一個似乎沒有在做什麼的函數：給任何輸入，|id| 都原封不動地把它送到輸出 ---
這也反映在他的型別 |a -> a| 上。
這個函數有什麼重要性呢？
原來，|(.)| 滿足結合律，並且以 |id| 為單位元素（這也是「單位函數」這名字的由來）：
```texonly
\begin{align*}
  |id . f| ~=&~ |f| ~=~ |f . id {-"~~,"-}|\\
  |(f . g) . h| ~&=~ |f . (g . h) {-"~~."-}|
\end{align*}
```
用數學術語來說的話，|id| 與 |(.)| 形成一個*幺半群* (*monoid*)。
\index{monoid 幺半群}
函數 |id| 的重要性就如同 |0| 在代數中的重要性（|0| 與 |(+)| 也是一個幺半群）。我們在許多計算、證明中都會見到它。

以下我們試著證明 |(.)| 的結合律。我們想論證
|(f . g) . h = f . (g . h)|，但該如何下手？
該等式的等號左右兩邊都是函數。
當我們說兩個整數相等，意思很清楚：如果等號左邊是 |0|, 右邊也是 |0|;
如果左邊是 |1|, 右邊也是 |1|... 但說兩個函數「相等」，是什麼意思呢？

::: {.definition title="外延相等(extensional equality)" #def:extensional-eq}
給定兩個型別相同的函數 |f| 和 |g|, 當我們說它們*外延相等*(*extensionally equal*)\index{extensional equality 外延相等}，
意思是給任何一個輸入，|f| 和 |g| 都算出相等的輸出。也就是：
|(forall x. f x = g x)|.

本書中，當我們寫兩個函數相等(|f = g|)時，指的便是外延相等，除非例外註明。
:::

在外延相等的假設下，證明 |(f . g) . h = f . (g . h)| 也就是證明對任何一個 |x|, |((f . g) . h) x = (f . (g . h)) x| 均成立. 我們推論如下：
```spec
  ((f . g) . h) x
=  {- |(.)| 的定義 -}
  (f . g) (h x)
=  {- |(.)| 的定義 -}
  f (g (h x))
=  {- |(.)| 的定義 -}
  f ((g . h) x) {-"~~."-}
=  {- |(.)| 的定義 -}
  (f . (g . h)) x {-"~~."-}
```
既然 |(f . g) . h = f . (g . h)|，我們便可統一寫成 |f . g . h|, 不用加括號了。

::: {.exlist}
::: {.exer #ex:identity-law}
證明 |id . f = f = f . id|.
:::
::: {.exans}
根據外延相等，我們需證明 |(forall x . id . f = f = f . id)|.
推論如下：
```spec
   (id . f) x
=    {- |(.)| 之定義 -}
   id (f x)
=    {- |id| 之定義 -}
   f x
=    {- |id| 之定義 -}
   f (id x)
=    {- |(.)| 之定義 -}
   (f . id) x {-"~~."-}
```
:::
:::

合成 |(.)| 也是一個中序運算子。和其他中序運算子一樣，其優先性低於函數應用。
因此，當我們寫 |f . g x|, 指的是 |f . (g x)| --- |g x| 為一個函數，
和 |f| 合成，而不是 |(f . g) x| （後者根據 |(.)| 的定義，是 |f (g x)|）。

::: {.example #eg:smaller-square-legal}
下列程式中，有些是合法的 Haskell 式子、有些則有型別錯誤。
對每個程式，如果它是合法的，請找出它的型別，並說說看該程式做什麼。
如果有型別錯誤，請簡述為什麼。

  1. |square . smaller 3|;
  2. |smaller 3 . square|;
  3. |smaller (square 3)|;
  4. |smaller . square 3|.


:::
::: {.answer}
前三者都是 |Int -> Int|。

  1. 根據 |(.)| 的定義，|(square . smaller 3) x = square (smaller 3 x)|.
因此 |square . smaller 3| 是一個函數，將其輸入和 |3| 比較，取較小者的平方。
  2. |(smaller 3 . square) x = smaller 3 (square x)|. 因此它讀入 |x|, 並在 |3| 或 |x^2| 之中選較小的那個。
  3. |smaller (square 3)| 是一個函數，讀入 |x| 之後，選擇 |x| 與 |3^2| 之中較小的那個。
  4. |smaller . square 3| 有型別錯誤： |square 3| 不是一個函數（而是一個整數），
無法和 |smaller| 合成。


:::



{title="函數應用運算子" #para:fun-apply}
本書中有些時候會將許多函數組合成一串，例如 |square . double . (+1) . smaller 3|
。由於函數應用的優先順序比一般二元運算元高，把上述式子應用在參數 |5| 之上時得寫成
```spec
  (square . double . (+1) . smaller 7) 5 {-"~~,"-}
```
{.nobreak}（這個式子的值為 $(2\times(5+1))^2$。）
每次都得加一對括號似乎有些累贅。Haskell 另有一個運算子|($)|, 唸作 ``apply'', 代表函數應用：
\index{\$@@{|($)|}}
```spec
($) :: (a -> b) -> a -> b
f $ x = f x {-"~~."-}
```
{.nobreak}|f $ x| 和 |f x| 意思一樣。那麼我們為何需要這個運算子呢？原因之一是
|($)| 的優先度比 |(.)| 低，因此上式可省去括號改寫如下：
```spec
  square . double . (+1) . smaller 7 $ 5 {-"~~."-}
```

運算子 |($)| 的另一個重要意義是：「函數應用」這個動作有了符號，
成為可以獨立討論的事物。例如，|($)| 可以當作參數。
一個這麼做的例子是習題 \@ref{ex:uncurry-apply}。

{title="常量函數" #para:const}
既然介紹了 |id|, 本節也順便介紹一個以後將使用到的基本組件。
給定 |x| 之後，函數 |const x| 是一個 *不論拿到什麼函數，都傳回 |x|*的函數。
函數 |const| 的定義如下：
```spec
const :: a -> b -> a
const x y = x {-"~~."-}
```
第\@ref{sec:evaluation}節開頭的範例 |three| 可定義為 |three = const 3|.

「無論如何都傳回 |x|」聽來好像是個沒用的函數，
但和 |id| 一樣，我們日後會看到它在演算、證明中時常用上。
事實上，*組件邏輯*理論告訴我們：所有函數都可以由 |id|, |const|, 和下述的 |subst| 三個函數組合出來。
```spec
subst :: (a -> b -> c) -> (a -> b) -> (a -> c)
subst f g x = f x (g x) {-"~~."-}
```

## $\lambda$ 算式 {#sec:lambda-terms}

雖說函數是一級市民，在本書之中，目前為止，仍有一項功能是其他型別擁有、函數卻還沒有的：寫出一個*未命名*的值的能力。
整數、真假值都能不經命名、直接寫在算式中，例如，
我們可寫 |smaller (square 3) 4|, 而不需要先定義好
::: {.texonly}
```
%format num1
%format num2
%format e1
%format e2
```
:::
```spec
num1, num2 :: Int
num1  = 3
num2  = 4 {-"~~,"-}
```
{.nobreak}才能說 |smaller (square num1) num2|. 但使用函數時，似乎非得
先給個名字，才能使用它：
```spec
square :: Int -> Int
square x = ... {-"~~,"-}
quad = twice square {-"~~."-}
```
{.nobreak}如果為了某些原因（例如，如果在我們的程式中 |square| 只會被用到一次），我們不想給 |square| 一個名字，我們能不能直接把它寫出來呢？

$\lambda$ 算式便是允許我們這麼做的語法。
以直觀的方式解釋，|\x -> e| 便是一個函數，其中 |x| 是參數，
|e| 是函數本體。
例如，|(\x -> x * x)| 是一個函數，計算其輸入(|x|)的平方。
如果我們不想給 |square| 一個名字, 我們可將 |quad| 定義為：
```spec
quad = twice (\x -> x * x) {-"~~."-}
```

寫成 $\lambda$ 算式的函數也可直接作用在參數上，例如 |(\x -> e1) e2|。
這個式子歸約的結果通常表示為|e1[e2/x]|,
意思是「將 |e1| 之中的 |x| 代換為 |e2|」。
例如，算式 |(\x -> x * x) (3+4)| 可歸約為 |(3+4) * (3+4)|.
::: {.example #lambda-examples}
以下是一些 $\lambda$ 算式的例子：

  * 函數 |(\x -> 1 + x)| 把輸入遞增 --- 和 |(1+)| 相同。
    其實，把 |(1+)| 的語法糖去掉後，得到的就是這個 $\lambda$ 算式。
  * |(\x -> \y -> x + 2 * x * y)| 是一個傳回 $\lambda$ 算式的函數。
    *  |(\x -> \y -> x + 2 * x * y) (3+4)| 可歸約為
       |(\y -> (3+4) + 2 * (3+4) * y)|。注意 |\x| 不見了，
       函數本體中的 |x| 被代換成 |3+4|，|\y -> ..| 則仍留著。
    * |(\x -> \y -> x + 2 * x * y) (3+4) 5| 可歸約為
      |(3+4) + 2 * (3+4) * 5|.
  * 由於傳回函數的函數是常見的，Haskell (如同 $\lambda$-calculus)
    提供較短的語法。上述例子中的函數也可簡寫成：
    |(\x y -> x + 2 * x * y)|.
  * 函數也可以當參數。例如，|(\x -> x 3 3) (+)| 可歸約為 |(+) 3 3|, 或 |3 + 3|.
  * 以下是 |(\f x -> f x x) (\y -> 2 * y) 3| 的求值過程：
```spec
   (\f x -> f x x) (\y z -> 2 * y + z) 3
=  (\x -> (\y -> 2 * y + z) x x) 3
=  (\y -> 2 * y + z) 3 3
=  2 * 3 + 3
=  9 {-"~~."-}
```
  * 在 |\x -> e| 之中，|x| 是範圍限於 |e| 的區域識別字。
    因此：
```spec
   (\f x -> x + f x) (\x -> x + x) 3
=  (\x -> x + (\x -> x + x) x) 3
=  3 + (\x -> x + x) 3
=  3 + 3 + 3
=  9 {-"~~."-}
```


:::

有了 $\lambda$ 算式後，函數 |smaller| 又有另一種寫法：
```spec
smaller :: Int -> Int -> Int
smaller = \x y -> if x <= y then x else y {-"~~."-}
```
事實上，$\lambda$ 算式可視為更基礎的機制 ---
目前為止我們所介紹的種種語法結構都僅是 $\lambda$ 算式的語法糖，都可展開、轉譯為 $\lambda$ 算式。
Haskell 的 $\lambda$ 算式源於一套稱為 *$\lambda$ 演算* (*$\lambda$ calculus*)的形式語言 --- 這是一個為了研究計算本質而發展出的理論，也是函數語言的理論核心。我們將在爾後的章節中做更詳盡的介紹。\todo{which?}

## 簡單資料型態 {#sec:elementary-datatypes}

藉由一些例子，我們已經看過 Haskell 的一些數值型別：|Int|, |Float| 等等。
在本節中我們將簡短介紹我們將用到的一些其他型別。

### 布林值 {#sec:boolean}

布林值 (Boolean)\index{Boolean 布林值}常用於程式中表達真和假。
在 Haskell 中，我們可假想有這樣的一個型別定義：
```spec
data Bool = False | True {-"~~."-}
```
{.nobreak}其中，|data| 是 Haskell 宣告新資料型別的保留字。
上述定義可用口語描述成「定義一個稱作 |Bool| 的新資料型別，
有兩個可能的值，分別為 |False| 和 |True|.」
|False| 和 |True| 是型別 |Bool| 的*唯二*兩個*建構元* ---
任何型別為 |Bool| 的值，如果有正規式，必定是它們兩者之一。
在 Haskell 之中，建構元必須以大寫英文字母或冒號(|:|)開頭。

{title="樣式配對"} \index{pattern matching 樣式配對} 有了資料，我們來看看怎麼定義該型別上的函數。以布林值為輸入的函數中，
最簡單又常用的可能是 |not|:
```spec
not :: Bool -> Bool
not False  = True
not True   = False {-"~~."-}
```
這和我們的的直覺理解一致：|not False| 是 |True|, |not True| 是
|False|. 我們看到這個定義寫成兩行（正式說來是兩個「子句」），\emph{每一個子句分別對應到 |Bool| 的一個可能的值}。
以下則是邏輯上的「且」和「或」（分別寫作|(&&)|與|(||||)|）的定義：%
^[邏輯「且」又稱作合取(conjunction)\index{conjunction 合取、且}；邏輯「或」又稱作析取(disjunction).\index{disjunction 析取、或}
在 Haskell 中，「且」與「或」需分別寫成 $(\mathtt{\&\&})$ 和 $(\mathtt{||||})$。本書中採用數學與邏輯領域較常使用的 |(&&)|與|(||||)|.]
```spec
(&&), (||) :: Bool -> Bool -> Bool
False  && y  = False
True   && y  = y {-"~~,"-}

False  || y  = y
True   || y  = True {-"~~."-}
```
運算子|(&&)|與|(||||)|的定義同樣是各兩個子句，每個子句分別考慮其第一個參數的值。
以 |x && y| 為例：如果 |x| 是 |False|, 不論 |y| 的值為何，|x && y| 都是 |False|；
如果 |x| 是 |True|, |x & y| 的值和 |y| 相同。|(||||)| 的情況類似。

::: {.example #eg:leap-year}
以下函數判斷給定年份 |y| 是否為閏年。
```haskell
leapyear :: Int -> Bool
leapyear y =  (y `mod` 4 == 0) &&
               (y `mod` 100 /= 0 || y `mod` 400 == 0) {-"~~."-}
```
:::
我們來算算看 |leapyear 2016|。依照定義展開為
```spec
  (2016 `mod` 4 == 0) && (2016 `mod` 100 /= 0 || 2016 `mod` 400 == 0) {-"~~."-}
```
接下來該怎麼做呢？函數 |(&&)| 的定義有兩個子句，我們得知道 |2016 `mod` 4 == 0| 的值才能得知該歸約成哪個。因此只好先算 |2016 `mod` 4 == 0|，得到 |True|:
```spec
  True && (2016 `mod` 100 /= 0 || 2016 `mod` 400 == 0) {-"~~,"-}
```
然後依照|(&&)| 的定義歸約為 |2016 `mod` 100 /= 0 |||| 2016 `mod` 400 == 0|.
接下來也依此類推。

我們發現這是第\@ref{sec:evaluation}節中所提及的*被迫求值*的例子：我們得先把參數算出，才知道接下來如何走。
函數 |not|, |(&&)|, |(||||)| 定義成許多個子句，每個都分析其參數的可能外觀，據此決定該怎麼走。這種定義方式稱作*樣式配對 (pattern matching)*：等號左手邊的 |False|, |True| 等等在此是樣式(pattern)。使用這些函數時，例如 |x && y| 中， |x| 得先被算到可以和這些樣式配對上的程度，才能決定接下來的計算如何進行。

樣式配對也可用在不止一個參數上。例如，以下的運算元 |(==)| 判斷兩個布林值是否相等。
```spec
(==) :: Bool -> Bool -> Bool
False  == False  = True
False  == True   = False
True   == False  = False
True   == True   = True {-"~~."-}
```
讀者可能注意到我們用了同一個符號 |(==)| 來表示整數與布林值的相等測試。
請讀者暫且接受，相信 Haskell 有某些方式可得知任一個算式中的 |(==)| 到底是什麼型別的相等。詳情 \todo{where?}

Haskell 中另有一個專用來做樣式配對的 |case| 算式。例如，|(&&)| 也可寫成如下的形式：
```spec
(&&) :: Bool -> Bool
x && y =  case x of
            False  -> False
            True   -> y {-"~~."-}
```
由於 |case| 是算式，如同 |let| 一樣可出現在其他算式中，也可巢狀出現。

:::{.exlist}
:::{.exer #ex:case-formula}
以 |case| 算式定義 |not|, |(||||)|, 和 |(==)|.
:::
:::{.exer #ex:equal-symbol-defn}
另一個定義 |(==) :: Bool -> Bool -> Bool| 的方式是
```spec
x == y = (x && y) || (not x && not y) {-"~~."-}
```
請將 |(x,y) := (False, False)|, |(x,y) := (False, True)|
等四種可能分別代入化簡，看看是否和本節之前的 |(==)| 定義相同。
:::
:::

### 字元 {#sec:char}

我們可把「字元」這個型別想成一個很長的 |data| 宣告：
```spec
data Char = 'a' | 'b' | ... | 'z' | 'A' | 'B' ....
```
{.nobreak}其中包括所有字母、符號、空白... 目前的 Haskell 甚至有處理 Unicode 字元的能力。
但無論如何，|Char| 之中的字元數目是有限的。我們可用樣式配對定義字元上的函數。
注意：字元以單引號括起來。

我們也可假設字元是有順序的，每個字元對應到一個內碼。
關於 |Char| 的常用函數中，|ord| 將字元的內碼找出，|chr| 則將內碼轉為字元：
```spec
ord  :: Char -> Int {-"~~,"-}
chr  :: Int -> Char {-"~~."-}
```
:::{.example #eg:isupper}
下列函數 |isUpper| 判斷一個字元是否為大寫英文字母；|toLower| 則將
大寫字母轉成小寫字母，若輸入並非大寫字母則不予以變動。
```haskell
isUpper :: Char -> Bool
isUpper c = let x = ord c in ord 'A' <= x && x <= ord 'Z' {-"~~,"-}

toLower :: Char -> Char
toLower c  | isUpper c  = chr (ord c - ord 'A' + ord 'a')
           | otherwise  = c {-"~~."-}
```
:::


### 序對 {#sec:pairs}

數學上，將兩個值（如 |3| 和 |'a'|) 放在一起，就成了一個*有序對*(*ordered pair*)，可寫成|(3,'a')|。\index{pair 序對}
之所以稱作「有序」對，因為其中兩個元素的順序是不可忽略的 --- |(3,'a')| 與 |('a',3)| 是不同的有序對。
另一個常見譯名是「數對」。由於我們處理的不只是數字，本書將之簡稱為「序對」。

給兩個集合 |A| 和 |B|, 從 |A| 之中任取一元素 |x|，從 |B| 之中也任取一元素 |y|，
兩者的序對 |(x,y)| 形成的集合稱作 |A| 和 |B| 的*笛卡兒積*(*Cartesian product*)，寫成 |A :* B|:\index{Cartesian product 笛卡兒積}
```spec
   A :* B = {(x,y) | x `mem` A, y `mem` B} {-"~~."-}
```
Haskell 之中也有類似的構造。給定型別 |a| 與 |b|, 它們的序對的型別是 |(a :* b)|.
^[然而，由於「程式可能不終止」這個因素作怪，|a :* b| 的元素並不僅是 |a| 與 |b| （如果視做集合）的笛卡兒積。詳見 \todo{where?}]
我們可以想像 Haskell 有這麼一個型別定義：
```spec
data (a :* b) = (a,b) {-"~~."-}
```
{.nobreak}以口語說的話，|(a :* b)| 是一個新型別，而具有此型別的值若有範式，必定是 |(x,y)| 的形式，其中 |x| 的型別是 |a|, |y| 的型別是 |b|.
^[其實這個定義並不符合 Haskell 的語法，因此只是方便理解的想像。另，型別 |(a :* b)| 在 Haskell 中寫成 |(a,b)|. 我的經驗中，讓型別與值的語法太接近，反易造成困惑。]
序對的建構元寫成|(,)|，型別為 |a -> b -> (a :* b)|.
例如 |(,) 4 'b' = (4,'b')|.

兩個常用的函數 |fst| 與 |snd| 分別取出序對中的第一個和第二個元素：
::: {.multicols}
::: {.mcol width="0.4\\textwidth"}
```spec
fst :: (a :* b) -> a
fst (x,y) = x {-"~~,"-}
```
:::
::: {.mcol width="0.4\\textwidth"}
```spec
snd :: (a :* b) -> b
snd (x,y) = y {-"~~."-}
```
:::
:::
函數 |fst| 與 |snd| 的定義方式也是樣式配對：輸入值必須先計算成 |(x,y)| 的形式。

::: {.example #eg:pairs-examples}
以下是一些序對與其相關函數的例子。

  * |(3,'a')| 是一個型別為 |(Int :* Char)| 的序對。
  * |fst (3,'a') = 3|, |snd (3,'a') = 'a'|
  * 函數 |swap| 將序對中的元素調換：
```spec
swap :: (a :* b) -> (b :* a)
swap (x,y) = (y,x) {-"~~."-}
```
另一個定義方式是 |swap p = (snd p, fst p)|.
但這兩個定義並不盡然相同。詳見第\@ref{sec:weak-head-normal-form}節。
:::

序對也可以巢狀構成。例如 |((True,3), 'c')| 是一個型別為 |((Bool :* Int) :* Char)| 的序對，而 |snd (fst ((True,3), 'c')) = 3|. 在 Haskell 之中，|((a :* b) :* c)| 與 |(a :* (b :* c))| 被視為不同的型別，但他們是*同構*的 --- 我們可定義一對函數在這兩個型別之間作轉換：
```haskell
assocr :: ((a :* b) :* c) -> (a :* (b :* c))
assocr ((x,y),z) = (x,(y,z)) {-"~~,"-}

assocl :: (a :* (b :* c)) -> ((a :* b) :* c)
assocl (x,(y,z)) = ((x,y),z) {-"~~,"-}
```
{.nobreak}並且滿足 |assocr . assocl = id|,  和 |assocl . assocr = id|.

:::{.exlist}
:::{.exer #ex:assocl-assocr}
試試看不用樣式配對，而以 |fst| 和 |snd| 定義 |assocl| 和 |assocr|:
```spec
assocl  p = ...
assocr  p = ...
```
:::
:::



:::{.infobox title="同構"}
\index{isomorphism 同構}
兩個集合|A|與|B| *同構*(*isomorphic*)，意思是
|A| 之中的 *每個*元素都*唯一地*對應到 |B| 之中的*一個*元素，反之亦然。

一個形式定義是：|A|與|B|同構意謂我們能找到兩個全(total)函數
\index{function 函數!total 全函數} |to :: A -> B| 和 |from :: B -> A|, 滿足
```spec
from . to = id {-"~~,"-}
to . from = id {-"~~."-}
```
此處的兩個 |id| 型別依序分別為 |A -> A| 和 |B -> B|。
將定義展開，也就是說，對所有 |x :: A|，|from (to x) = x|; 對所有 |y :: B|, |to (from y) = y|. 這個定義迫使對每個 |x| 都存在一個唯一的 |to x|, 反之亦然。

我們已有兩個例子：|((a :* b) :* c)| 與 |(a :* (b :* c))| 同構，此外，|(a :* b)| 與 |(b :* a)| 也同構，因為 |swap . swap = id|.

如果集合|A|與|B|同構，不僅 |A| 之中的每個元素都有個在 |B| 之中相對的元素，給任一個定義在 |A| 之上的函數 |f|, 我們必可構造出一個 |B| 之上的函數，具有和 |f| 相同的性質。即使|A|與|B|並不真正相等，我們也可把它們視為*基本上沒有差別*的。在許多無法談「相等」的領域中，同構是和「相等」地位一樣的觀念。
:::

另外可一提的是，Haskell 允許我們在 $\lambda$ 算式中做樣式配對。例如 |fst| 的另一種寫法是：
```spec
fst = \(x,y) -> x {-"~~."-}
```

Haskell 另有提供更多個元素形成的有序組，例如 |(True, 3, 'c')| 是一個型別為 |(Bool :* Int :* Char)| 的值。但本書暫時不使用他們。

{title="分裂與積" #par:split-product}
在我們將介紹的程式設計風格中，以下兩個產生序對的運算子相當好用。
第一個運算子利用兩個函數產生一個序對：
```haskell
fork :: (a -> b) -> (a -> c) -> a -> (b :* c)
(fork f g) x = (f x, g x) {-"~~."-}
```
{.nobreak}給定兩個函數 |f :: a -> b| 和 |g :: a -> c|,
|fork f g :: a -> (b :* c)| 是一個新函數，將 |f| 和 |g| 的結果
收集在一個序對中。
我們借用範疇論的詞彙，將此稱作*分裂*(*split*) ---
|fork f g| 可讀成「|f| 與 |g| 的分裂」。
\index{pair 序對!split 分裂}

如果我們已經有了一個序對，我們可用 |(f *** g)| 算出一個新序對：
```spec
(***) :: (a -> b) -> (c -> d) -> (a :* c) -> (b :* d)
(f *** g) (x,y) = (f x, g x) {-"~~."-}
```
{.nobreak}函數|(f *** g)| 將 |f| 和 |g| 分別作用在序對 |(x,y)| 的兩個元素上。
這個操作稱作「|f| 和 |g| 的乘績(product)」，同樣是借用範疇論的詞彙。
\index{pair 序對!product 乘績}

關於分裂與乘積，有兩條重要的性質，將會在之後用到：
:::{.equations}
  * {title="吸收律" #eq:prod-split-absorb} |(f *** g) . fork h k| |= fork (f . h) (g . k)|
  * {title="融合律" #eq:prod-fusion} |(f *** g) . (h *** k)| |= ((f . h) *** (g . k))|



:::

目前 Haskell 的標準階層函式庫將分裂與乘積收錄在 \texttt{Control.Arrow} 中，
|fork f g| 寫作：\texttt{f \&\&\& g}, |(f *** g)| 則寫作 \texttt{f *** g}.

{title="Currying 與 Uncurrying" #par:currying-uncurrying}
如前所述，Haskell 的每個函數都只拿一個參數。拿多個參數的函數可以
傳回函數的函數來模擬，稱作 currying.
有了序對之後，另一種模擬多參數的方式是把參數都包到一個序對中。
例如，型別為 |(a :* b) -> c)| 的函數可視為拿了兩個型別為 |a| 與 |b| 的參數。

函數 |curry| 與 |uncurry| 幫助我們在這兩種表示法之間轉換 ---
|curry| 將拿序對的函數轉換成 curried 函數，\index{currying}
|uncurry| 則讓 curried 函數改拿序對當作參數：\index{currying!uncurrying}
```spec
curry :: ((a :* b) -> c) -> (a -> b -> c)
curry f x y = f (x,y) {-"~~,"-}

uncurry :: (a -> b -> c) -> ((a :* b) -> c)
uncurry f (x,y) = f x y {-"~~."-}
```
{.nobreak}例：如果|(==)| 的型別為 |Int -> Int -> Bool|,
|uncurry (==)| 的型別為 |(Int :* Int) -> Bool|。
後者檢查一個序對中的兩個值是否相等（例：|uncurry (==) (3,3) = True|）。

:::{.exlist}
:::{.exer #ex:curry-uncurry-id}
事實上，|curry| 與 |uncurry| 的存在證明了 |(a :* b) -> c|
與 |a -> b -> c| 是同構的。試證明
|curry . uncurry = id|, 以及 |uncurry . curry = id|.
:::
:::{.exans}
欲證明 |curry . uncurry = id|：
```spec
     curry . uncurry = id
<=>    {- 外延相等及 |id| 之定義 -}
     (forall f : curry (uncurry f) = f)
<=>    {- 外延相等 -}
     (forall f x y : curry (uncurry f) x y = f x y) {-"~~."-}
```
{.nobreak}因此我們證明 |curry (uncurry f) x y = f x y| 如下：
```spec
   curry (uncurry f) x y
=   {- |curry| 之定義 -}
   uncurry f (x,y)
=   {- |uncurry| 之定義 -}
   f x y  {-"~~."-}
```

與此相似，欲證明 |uncurry . curry = id| 我們須證明
|uncurry (curry f) (x,y) = f (x,y)|，其證明也與上面的證明類似。
:::
:::{.exer #ex:uncurry-apply}
請說明 |map (uncurry ($))| 的型別與功能。
關於 |($)| 請參考第\pageref{para:fun-apply}頁。
:::
:::{.exans}
|map (uncurry ($)) :: List ((a -> b) :* a) -> List b|.
它拿一個內容均為「(函數 $\times$ 參數)」序對的串列，將每個函數作用在其參數上。
例如：
```spec
map (uncurry ($)) [((1+), 3), (square, 4), (smaller 5, 3)]
```
{.nobreak}會得到 |[1+3,4*4,3]|.
:::
:::


## 弱首範式 {#sec:weak-head-normal-form}

我們現在可把第\@ref{sec:evaluation}節中提及的求值與範式談得更仔細些。
第一次閱讀的讀者可把本節跳過。
回顧 |fst| 使用樣式配對的定義 |fst (x,y) = x|.
假設我們把 |swap| 定義如下：
```spec
swap p = (snd p, fst p) {-"~~."-}
```
{.nobreak}考慮 |fst (swap (3,'a'))| 該怎麼求值：
```spec
   fst (swap (3,'a'))
=   {- |swap| 的定義 -}
   fst (snd (3,'a'), fst (3,'a'))
=   {- |fst| 的定義 -}
   snd (3,'a')
=   {- |snd| 的定義 -}
   'a' {-"~~."-}
```
{.nobreak}在第一步中，由於 |fst| 使用樣式配對，我們得先把 |swap (3,'a')| 算出來。
若把 |swap (3,'a')| 算到底，得到的範式是 |('a',3)|.
但如第一步中所顯示，如果目的只是為了配對 |(x,y)| 這個樣式，
我們並不需要把 |swap (3,'a')| 算完，只需算到 |(snd (3,'a'), fst (3,'a'))|
即可 --- |x| 可對應到 |snd (3,'a')|, |y| 可對應到 |fst (3,'a')|,
|fst| 的計算便可以進行。在下一步中，子算式 |fst (3,'a')| 便被丟棄了，
並沒有必要算出來。

做樣式配對時，Haskell 只會把算式歸約到剛好足以與樣式配對上的程度。
當樣式的深度只有一層（如|(x,y)|）時，與之配對的式子會被歸約成一種
稱作*弱首範式*(*weak head normal form*)%
\index{normal form 範式!weak head 弱首範式}的形式。
弱首範式有其嚴格定義，但本書讀者只需知道：算式會被歸約到*露出最外面的建構元*，（在此例中是被歸約成 |(_,_)| 的形式），然後便停下來。

::: {.example #eg:swap}
回顧 |swap| 的兩種定義方式，分別命名為
```texonly
%format swap1
%format swap2
```
```spec
swap1 (x,y)  = (y,x)  {-"~~,"-}
swap2 p      = (snd p, fst p) {-"~~,"-}
```
若考慮不終止的參數，兩者的行為並不盡然相同。
定義 |three (x,y) = 3|, 並
假設 |undefined| 是一個沒有範式的式子 --- 一旦開始對 |undefined| 求值，便停不下來。
試計算 |three (swap1 undefined)| 和 |three (swap2 undefined)|.
:::
:::{.answer}
由於 |three| 使用樣式配對，計算 |three (swap1 undefined)| 時得把 |swap1 undefined| 歸約成弱首範式。
同理，計算 |swap1 undefined| 時，第一步便是先試圖把 |undefined| 歸約成弱首範式，然後便停不下來了。

至於 |three (swap2 undefined)| 則可如下地求值：
```spec
   three (swap2 undefined)
=   {- |swap2| 之定義 -}
   three (snd undefined, fst  undefined)
=   {- |three| 之定義 -}
   3 {-"~~."-}
```
{.nobreak}第一步中，|swap2 undefined| 則依照範式順序求值的原則展開為 |(snd undefined, fst  undefined)| --- 這是一個序對，只是該序對含有兩個沒有範式的元素。
該序對可對應到樣式 |(x,y)|, 因此整個式子歸約為 |3|.

附帶一提，|three undefined| 是一個不停止的計算。
:::

## 串列 {#sec:lists}

一個\emph{串列}(list)\index{list 串列}
抽象說來便是*將零個或多個值放在一起變成一串*。
串列是函數語言傳統上的重要資料結構：
早期的函數語言 LISP 便是 LISt Processing 的縮寫。
Haskell 中的串列多了一個限制：串列中的每個元素必須有同樣的型別。
本書中將「元素型別均為 |a| 的串列」的型別寫成 |List a|.
^[Haskell 中的寫法是 |[a]|. 同樣地，在我的教學經驗中，將中括號同時使用在值與型別上造成不少誤解。例如學生可能認為 |[1,2]| 的型別是 |[Int,Int]| --- 其實應該是 |[Int]|.]
Hasekell 以中括號表示串列，其中的元素以逗號分隔。
例如，|[1,2,3,4]| 是一個型別為 |List Int| 的串列，其中有四個元素；
|[True, False, True]| 是一個型別為 |List Bool| 的串列，有三個元素。
至於 |[]| 則是沒有元素的*空串列*（通常唸做 ``nil''），其最通用的型別為 |List a|，
其中 |a| 可以是任何型別。

串列的元素也可以是串列。例如 |[[1,2,3],[],[4,5]]| 的型別是 |List (List Int)|,
含有三個元素，分別為 |[1,2,3]|, |[]|, 和 |[4,5]|.

事實上，上述的寫法只是語法糖。我們可想像 Haskell 有這樣的型別定義：
```spec
data List a {-"\,"-}={-"\,"-} [] {-"\,"-}|{-"\,"-} a : List a {-"~~."-}
```
{.nobreak}意謂一個元素型別為 |a| 的串列只有兩種可能構成方式：
可能是空串列 |[]|，也可能是一個元素 (|a|) 接上另一個串列 (|List a|)。
後者的情況中，元素和串列之間用符號 |(:)| 銜接。
\index{[]@@{|[]|}}
\index{:@@{|(:)|}}

符號 |(:)| 唸作 ``cons'', 為「建構(construct)」的字首。
其型別為 |a -> List a -> List a| ---
它總是將一個型別為 |a| 的元素接到一個 |List a| 之上，造出另一個 |List a|.
上述的 |[1,2,3,4]| 其實是 |1 : (2 : (3 : (4 : [])))|
的簡寫：由空串列 |[]| 開始，將元素一個個接上去。
為了方便，Haskell 將 |(:)| 運算元視做右相依的，
因此我們可將括號省去，寫成
|1 : 2 : 3 : 4 : []|。

:::{.infobox title="|(:)| 與 |(::)|"}
\index{:@@{|(:)|}}\index{::@@{|(::)|}}
大部分有型別的函數語言（如 ML, Agda 等）之中，
|(:)| 表示型別關係，|(::)| 則是串列的建構元。
Haskell 的前身之一是 David A. Turner 的語言 Miranda.
在其 Hindley-Milner 型別系統中，Miranda 使用者幾乎不需寫出程式的型別 ---
型別可由電腦自動推導。而串列是重要資料結構。
把兩個符號調換過來，使常用的符號較短一些，似乎是合理的設計。

Haskell 繼承了 Miranda 的語法。
然而，後來 Haskell 的型別發展得越來越複雜，
使用者偶爾需要寫出型別來幫助編譯器。
即使型別簡單，程式語言界也漸漸覺得將函數的型別寫出是好習慣。
而串列建構元的使用量並不見得比型別關係多。
但此時想改符號也為時已晚了。
:::

無論如何，這樣的串列表示法是偏一邊的 ---
元素總是從左邊放入，最左邊的元素也最容易取出。
如果一個串列不是空的，其最左邊的元素稱作該串列的*頭*(*head*)，
剩下的元素稱作其*尾*(*tail*)。
例如，|[1,2,3,4]| 的頭是 |1|, 尾是 |[2,3,4]|.

Haskell 中將字串當作字元形成的串列。標準函式庫中這麼定義著：
```spec
type String = List Char {-"~~."-}
```
{.nobreak}意謂 |String| 就是 |List Char|。
在 Haskell 中，|data| 用於定義新型別，而 |type| 並不產生一個新的型別，
只是給現有的型別一個較方便或更顯出當下意圖的名字。
此外，Haskell 另提供一個語法糖，用雙引號表達字串。
因此，|"fun"| 是 |['f','u','n']| 的簡寫，
後者又是 |'f':'u':'n':[]| 的簡寫。

本節接下來將介紹許多與串列相關的內建函數。

### 串列解構 {#sec:list-deconstruct}

我們先從拆解串列的函數開始。函數 |head| 和 |tail| 分別取出一個串列的頭和尾：
:::{.multicols}
:::{.mcol width="0.4\\textwidth"}
```spec
head :: List a -> a
head (x:xs) = x {-"~~,"-}
```
:::
:::{.mcol width="0.4\\textwidth"}
```spec
tail :: List a -> List a
tail (x:xs) = xs {-"~~."-}
```
:::
:::
{.nobreak}注意其型別：|head| 傳回一個元素，|tail| 則傳回一個串列。
例：|head "fun"| 和 |tail "fun"| 分別是字元 |'f'| 和字串 |"un"|.
函數 |head| 和 |tail| 都可用樣式配對定義，但此處的樣式並不完整，尚缺 |[]| 的情況。
如果將空串列送給 |head| 或 |tail|，則會出現執行時錯誤。
因此，|head| 和 |tail| 都是*部分函數*(*partial functions*) --- 它們只將某些值（非空的串列）對應到輸出，某些值（空串列）則沒有。\index{function 函數!partial 部分函數}

函數 |null| 判斷一個串列是否為空串列。它也可用樣式配對定義如下：
```spec
null :: List a -> Bool
null []      = True
null (x:xs)  = False {-"~~."-}
```
{.nobreak}本書依循 @Bird:98:Introduction 中的變數命名習慣，
將型別為串列的變數以 |s| 做結尾，例如 |xs|, |ys| 等等。
至於「元素為串列的串列」則命名為 |xss|, |yss| 等等。
但這只是為方便理解而設計的習慣。Haskell 本身並無此規定。

除了 |head| 與 |tail|，也有另一組函數 |last| 與 |init| 分別取出一個串列*最右邊*的元素，以及剩下的串列：
```spec
last  :: List a -> a {-"~~,"-}
init  :: List a -> List a {-"~~."-}
```
{.nobreak}例：|last "fun"| 與 |init "fun"| 分別為字元 |'n'| 與字串 |"fu"|.
但 |last| 與 |init| 的定義比起 |head| 與 |tail| 來得複雜：
記得我們的串列表示法是偏向一邊的，從左邊存取元素容易，從右邊存取元素則較麻煩。
我們會在 \todo{where} 之中談到 |last| 與 |init| 的定義。


### 串列生成 {#sec:list-generation}

第\@ref{sec:list-deconstruct}節中的函數均將串列拆開。
本節之中我們來看一些生成串列的方法。
如果元素的型別是有順序的（例如|Int|, |Char|等型別），Haskell 提供了一個
方便我們依序生成串列的語法。以例子說明：
::: {.example #eg:list-gen-examples}
以下為 Haskell 的列舉語法的一些例子：

  * |[0..10]| 可展開為 |[0,1,2,3,4,5,6,7,8,9,10]|.
  * 可用頭兩個元素來指定間隔量。例如 |[0,3..10] = [0,3,6,9]|. 注意該串列的元素不超過右界 |10|.
  * 在 |[10..0]| 之中，|10| 一開始就超過了右界 |0|, 因此得到 |[]|. 如果想要產生由 |10| 倒數到 |0| 的串列，可這樣指定間隔：|[10,9..0]|.
  * 字元也是有順序的，因此 |['a'..'z']| 可展開為含所有英文小寫字母的串列。
  * 至於沒有右界的 |[0..]| 則會展開為含 |[0,1,2,3...]| 的無限長串列。


:::


函數 |iterate :: (a -> a) -> a -> List a| 用於產生無限長的串列：
|iterate f x| 可展開為 |[x, f x, f (f x), f (f (f x))... ]|.
::: {.example #eg:iterate-example}
一些 |iterate| 的例子：

  * |iterate (1+) 0| 展開為 |[0,1,2,3...]|. 其實 |[n..]| 可視為 |iterate (1+) n| 的簡寫。
  * 在例\@ref{ex:fromto-takeWhile-iterate}中我們會看到 |[m..n]| 也可用 |iterate| 與其他函數做出。
  * |iterate not False| 可得到無窮串列 |[False, True, False...]|.


:::

數學中描述集合時常使用一種稱作集合建構式(set comprehension)的語法。例如，
|{x * x || x `mem` S, odd x}| 表示收集所有 |x*x| 形成的集合，其中
|x| 由集合 S 中取出，並且必須為奇數。Haskell 將類似的語法用在串列上。
同樣以例子說明：
::: {.example #eg:list-comprehension-examples}
串列建構式(list comprehension)的例子：\index{list 串列!comprehension 串列建構式}

  * |[x || x <- [0..9]]| 表示「從|[0..9]|之中取出 |x|, 並收集 |x|」，可展開為 |[0,1,2,3,4,5,6,7,8,9]|.
  * |[x*x || x <- [0..10]]| 的 |x| 來源和之前相同，但收集的是 |x*x|，得到 |[0,1,4,9,25,36,49,64,81]|.
  * |[(x,y) || x <- [0..2], y <- "abc"]| 展開得到
    |[(0,'a'),| |(0,'b'),| |(0,'c'),| |(1,'a'),| |(1,'b'),| |(1,'c'),| |(2,'a'),| |(2,'b'),| |(2,'c')]|.
    注意序對出現的順序：先固定 |x|，將 |y| 跑過一遍，再換成下一個 |x|.
  * |[x*x || x <- [0..10], odd x]| 從|[0..10]|之中取出 |x|，但只挑出滿足 |odd x| 的那些，得到 |[1,9,25,49,81]|.


:::

::: {.example #eg:list-comprehension-examples2}
以下算式的值分別為何？

  1. |[(a,b) || a <- [1..3], b <- [1..2]]|.
  2. |[(a,b) || b <- [1..2], a <- [1..3]]|.
  3. |[(i, j) || i <- [1..4], j <- [(i + 1)..4]]|. 這是一個有了 |i <- ..| 之後，|i| 即可在右方被使用的例子。
  4. |[(i, j) || i <- [1..4], even i, j <- [(i + 1)..4], odd j]|.
  5. |['a' ||i <- [0..10]]|. 這個例子顯示 |i| 並不一定非得出現在被收集項目中。


:::

::: {.answer}
分別展開如下：

  1. |[(1,1),(1,2),(2,1),(2,2),(3,1),(3,2)]|.
  2. |[(1,1),(2,1),(3,1),(1,2),(2,2),(3,2)]|.
  3. |[(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]|.
  4. |[(2,3)]|.
  5. |"aaaaaaaaaaa"|.


:::

串列建構式在寫程式時相當好用，但它也僅是個語法糖 ---
所有的串列建構式都可轉換為後面的章節將介紹的 |map|, |concat|, |filter| 等函數的組合。

### 串列上的種種組件函數 {#sec:list-combinators}

我們將在本節介紹大量與串列有關的函數。
它們常被稱做*組件*(*combinators*)\index{combinator 組件}函數。
每一個組件都負責一項單一、但具通用性而容易重用的功能。
它們常用來彼此結合以組出更大的程式。

介紹這些函數有兩個原因。首先，它們可用來組出許多有趣的程式。
我們將一邊逐一介紹這些函數，一邊以例子示範，
同時也逐漸帶出本章鼓勵的一種特殊編程風格。
另一個原因是在日後的章節中我們也都將以這些函數作為例子，
討論並證明關於它們的性質。

第一次閱讀的讀者可能訝異：這麼多函數，怎麼記得住？
事實上，這些組件大都僅是把常見的編程模式具體地以形式方式表達出來。
辨識出這些模式後，不僅會發現它們其實很熟悉，對於我們日後了解其他程式也有助益。

{title="長度"} 函數 |length :: List a -> Int| 計算串列的長度。
空串列 |[]| 的長度為 |0|. 例：|length "function" = 8|.

{title="索引"} 函數 |(!!)| 的型別為 |List a -> Int -> a|.
給定串列 |xs| 和整數 |i|, 如果 |0 <= i < length xs|,
|xs !! i| 為 |xs| 中的第 |i| 個元素，但由 |0| 起算。
例 |"function" !! 0 = 'f'|, |"function" !! 3 = 'c'|.
如果 |i > length xs|, 則會成為執行期錯誤。
注意：如果 |length xs = n|，其中的元素編號分別為 |0|, |1| .. |n-1|.

在指令式語言中，索引是處理陣列常用的基本操作。
處理陣列的常見模式是用一個變數|i|指向目前正被處理的元素，將|a[i]|的值讀出或覆寫，
然後更新|i|的值。
但由接下來的許多範例中，讀者會發現本章盡量避免這種做法。
也因此 |(!!)| 在本章中使用的機會不多。


{title="連接"} 函數 |(++) :: List a -> List a -> List a| 將兩個串列相接。
例：|[1,2,3] ++ [4,5] = [1,2,3,4,5]|.

函數 |(++)| 和 |(:)| 似乎都是把串列接上東西。兩者有什麼不同呢？
答案是：|(:) :: a -> List a -> List a| 永遠把*一個*元素接到串列的左邊，
而 |(++)| 把兩個串列接在一起，兩個串列都有可能含有零個或多個元素。
例：|[] ++ [4,5] = [4,5]|. 事實上，|(:)| 是比 |(++)| 更基礎的操作。
在第\@ref{sec:induction-lists-defn}節中，我們會看到 |(++)| 是用 |(:)| 定義而成的。

另一個關於連接的函數是 |concat :: List (List a) -> List a|：它以一個元素都是串列的串列作為輸入，將其中的串列接在一起。例：|concat [[1,2,3],[],[4],[5,6]]| |=| |[1,2,3,4,5,6]|. 它和 |(++)| 的不同之處在哪呢？顯然，|(++)| 總把兩個串列接在一起，
而 |concat| 的參數中可含有零個或多個串列。
在第\@ref{sec:induction-lists-defn}節中，我們會看到 |concat| 是用 |(++)| 定義而成的。

{title="取與丟"} |take| 的型別為 |Int -> List a -> List a|.
|take n xs| 取 |xs| 的前 |n| 個元素。若 |xs| 的長度不到 |n|,
|take n xs| 能拿幾個就拿幾個. 例：|take 3 "function" = "fun"|,
|take 5 "ox" = "ox"|.


相對地，|drop n xs| 丟掉 |xs| 的前 |n| 個元素。若 |xs| 的長度不到 |n|,
|drop n xs| 能丟幾個就拿幾個. 例：|drop 3 "function" = "ction"|,
|take 5 "ox" = ""|. 函數 |drop| 的型別也是 |Int -> List a -> List a|.

函數 |take| 和 |drop| 顯然有些關聯，但它們的關聯該怎麼具體地寫下來呢？
一個可能是：對所有的 |n| 和 |xs|,
```texonly
\begin{equation*}
   |take n xs ++ drop n xs = xs| \mbox{~~.}
   \label{eq:taken-dropn}
\end{equation*}
```
{.nobreak}乍看之下似乎言之成理。但這個性質真的成立嗎？
我們將在第\@ref{ch:induction}章中討論到。


{title="映射"} |map :: (a -> b) -> List a -> List b| 是串列上
一個很重要的高階函數：|map f xs| 將 |f| 作用在 |xs| 的每一個元素上。
例：
```texonly
\begin{align*}
|map square [1,2,3,4]| &= |[1,4,9,16]| \mbox{~~,}\\
|map (1+) [2,3,4]| &= |[3,4,5]| \mbox{~~.}
\end{align*}
```
{.nobreak}回憶我們之前關於高階函數的討論，另一個理解方式是：
|map| 是一個處理函數的操作。給一個「將 |a| 變成 |b|」的函數 |f :: a -> b|，
|map| 將這個函數*提升*到串列的層次，
得到一個「將 |List a| 變成 |List b|」的函數 |map f :: List a -> List b|.

:::{.example #ex:inits}
如果一個串列 |xs| 可分解為 |ys ++ zs|, 我們說 |ys| 是 |xs| 的一個*前段(prefix)*,\index{list 串列!prefix 前段}
|zs| 則是 |xs| 的一個*後段*(*suffix*). \index{list 串列!suffix 後段}
例如，串列 |[1,2,3]| 的前段包括 |[]|, |[1]|, |[1,2]|, 與|[1,2,3]| （注意：|[]|是一個前段，|[1,2,3]| 本身也是）, 後段則包括 |[1,2,3]|, |[2,3]|, |[3]|, 與 |[]|。

試定義函數 |inits :: List a -> List (List a)|, 計算輸入串列的所有前段。
^[請注意該函數的名字是 |inits|, 和之前介紹過的 |init| 不同。這是 Haskell 函式庫中使用的命名。]
{\bf 提示}：目前我們可以用 |map|, |take| 和其他函數組出 |inits|.
在第\@ref{sec:more-inductive-defns}節中將會介紹另一個做法。
:::
:::{.answer}
一種使用 |map| 和 |take| 的可能作法如下：
```spec
inits :: List a -> List (List a)
inits xs = map (\n -> take n xs) [0 .. length xs] {-"~~."-}
```
{.nobreak}或著也可用串列建構式寫成 |[take n xs || n <- [0.. length xs]]|.
讀者可能已發現：|[f x || x <- xs]| 就是 |map f xs|.
:::

:::{.exlist}
:::{.exer #ex:tails}
定義函數 |tails :: List a -> List (List a)|,
計算輸入串列的所有後段。
:::
::: {.exans .compact}
```spec
tails :: List a -> List (List a)
tails xs = map (\n -> drop n xs) [0 .. length xs] {-"~~."-}
```
:::
:::

{title="過濾"}
一個型別為 |a -> Bool| 的函數稱作一個「述語」(predicate).
\index{predicate 述語}
給定述語 |p|, |filter p xs| 將 |xs| 之中滿足 |p| 的元素挑出。
函數 |filter| 的型別為 |(a -> Bool) -> List a -> List a|。
例：|filter even [2,5,1,7,6] = [2,6]|.

:::{.example #eg:numUpper}
該怎麼得知一個字串中大寫字母的個數？
將大寫字母過濾出來，計算所得串列的長度即可。如下所示：
```spec
numUpper :: String -> Int
numUpper = length . filter isUpper {-"~~."-}
```
:::

:::{.example #eg:map-square}
下列算式求出$0^2$ 到 $50^2$ 的平方數（能寫成 $n^2$ 的數字）中，
結尾為 $25$ 的數字。
```spec
  filter ((==25) . (`mod` 100)) (map square [0..50]) {-"~~."-}
```
{.nobreak}歸約後得到 |[25,225,625,1225,2025]|.
其中 |(==25) . (`mod` 100)| 部分使用了第\@pageref{par:binary-operator-sectioning}頁
中提到的語法。如果覺得不習慣，也可用 $\lambda$ 算式寫成：
```spec
  filter (\ n -> n `mod` 100 == 25) (map square [0..50]) {-"~~."-}
```
:::

:::{.example #eg:map-square-2}
接續上例。另一個可能寫法是先過濾出「平方之後結尾為 |25|」的數字，
再算這些數字的平方：
```spec
  map square (filter ((==25) . (`mod` 100) . square) [0..50]) {-"~~."-}
```
{.nobreak}這個算式也歸約出一樣的結果：|[25,225,625,1225,2025]|。

稍微推廣一些，這個例子暗示我們 |filter p . map f| 和 |map f . filter (p . f)| 似乎是等價的。
但確實如此嗎？我們也將在第\@ref{ch:induction}章中討論。
:::

:::{.example #eg:map-square-fork}
接續上例。如果我們不僅希望找到結尾為 $25$ 的平方數，也希望知道它們是什麼數字的平方，
一種寫法如下：
```spec
  filter ((==25) . (`mod` 100) . snd) (map (fork id square) [0..50]) {-"~~."-}
```
{.nobreak}我們用 |map (fork id square)| 將每個數字與他們的平方放在一個序對中，
得到|[(0,0), (1,1), (2,4), (3,9)...]|.
而 |filter| 的述語多了一個 |snd|, 表示我們只要那些「第二個元素符合條件」的序對。
上式化簡後可得到 |[(5,25),| |(15,225),| |(25,625),| |(35,1225),| |(45,2025)]|.
運算元 |fork| 的定義詳見第\@pageref{par:split-product}頁。

述語 |(==25) . (`mod` 100) . snd| 可以展開為 |(\(i,n) -> n `mod` 100 == 25)|.
:::

{title="取、丟、與過濾"} 函數 |takeWhile|, |dropWhile| 和 |filter| 有一樣的型別。
```spec
takeWhile  :: (a -> Bool) -> List a -> List a {-"~~,"-}
dropWhile  :: (a -> Bool) -> List a -> List a {-"~~."-}
```
它們之間的差異也許用例子解釋得最清楚：
```spec
filter     even [6,2,4,1,7,8,2] = [6,2,4,8,2] {-"~~,"-}
takeWhile  even [6,2,4,1,7,8,2] = [6,2,4] {-"~~,"-}
dropWhile  even [6,2,4,1,7,8,2] = [1,7,8,2] {-"~~."-}
```
|filter p| 挑出所有滿足 |p| 的元素；
|takeWhile p| 由左往右逐一取出元素，直到遇上第一個不滿足 |p| 的元素，並將剩下的串列丟棄；
|dropWhile p| 則與 |takeWhile p| 相對，將元素丟棄，直到遇上第一個不滿足 |p| 的元素。
直覺上，後兩者似乎也應該滿足 |takeWhile p xs ++ dropWhile p xs = xs|, 但這仍尚待驗證。

:::{.example #eg:fromto-takeWhile-iterate}
給定整數 |m| 與 |n|, |[m..n]| 可視為 |takeWhile (<= n) (iterate (1+) m)| 的簡寫。
:::

:::{.example #eg:takeWhile-dropWhile-until}
讀者也許覺得 |takeWhile| 或 |dropWhile| 似乎和迴圈有密切關係。
確實，利用 |iterate| 與 |dropWhile|，我們可定義出類似 |while| 迴圈的操作：
```haskell
until :: (a -> Bool) -> (a -> a) -> a -> a
until p f = head . dropWhile (not . p) . iterate f
```
{.nobreak}|until p f x| 由 |x| 算出 |f x|, 由 |f x| 算出 |f (f x)| ...
直到 |p (f (f .. x))| 成立為止。例：
|until ((> 50) . square) (1+) 0| 得到 |8|, 因為 $8^2 = 64$,
是第一個平方大於 $50$ 的非負整數。
由於惰性求值，|iterate f| 在意義上雖然是個無窮串列，
但只會被執行到 |dropWhile (not . p)| 擷取的長度為止。

下述函數則實作了用輾轉相減法求最大公因數的古典演算法。函數 |minus| 不斷
將大數減去小數，直到兩數相等為止：
```haskell
gcd :: (Int :* Int) -> Int
gcd = fst . until (uncurry (==)) minus {-"~~,"-}
  where minus (x,y)  | x > y = (y, x-y)
                     | x < y = (y-x, x) {-"~~."-}
```
{.nobreak}關於 |uncurry| 詳見第\@pageref{par:currying-uncurrying}頁。
:::

:::{.exlist}
:::{.exer #ex:squaresUpTo}
試定義一個函數
|squaresUpTo :: Int -> List Int|, 使得 |squaresUpTo n| 傳回
所有不大於 |n| 的平方數。例：|squaresUpTo 10 = [1,4,9]|,
|squaresUpTo (-1) = []|.
:::
::: {.exans .compact}
```haskell
squaresUpTo :: Int -> List Int
squaresUpTo n = takeWhile (<= n) (map square [0..]) {-"~~."-}
```
:::
:::


{title="拉鍊"}
函數 |zip :: List a -> List b -> List (a :* b)| 的作用可由下述例子示範：
```spec
zip [1,2,3]  "abc"  = [(1,'a'), (2,'b'), (3,'c')] {-"~~,"-}
zip [1,2]    "abc"  = [(1,'a'), (2,'b')] {-"~~,"-}
zip [1,2,3]  "ab"   = [(1,'a'), (2,'b')] {-"~~,"-}
zip [1..]    "abc"  = [(1,'a'), (2,'b'), (3,'c')] {-"~~,"-}
zip [1..]    [2..]  = [(1,2), (2,3), (3,4) ..] {-"~~,"-}
```
{.nobreak}|zip xs ys| 將串列 |xs| 與 |ys| 相對應的元素放在序對中。
如果兩個串列長度不同，|zip| 將其中一個用完後即停止。
|zip| 也能處理無限長的串列。
由於這個動作看來像是把|xs|與|ys|當作拉鍊的兩側「拉起來」，因此用拉拉鍊的狀聲詞 ``zip'' 命名。

相對地，也有一個函數 |unzip :: List (a :* b) -> (List a :* List b)|，
將「拉鍊」拉開。例：|unzip [(1,'a'), (2,'b'), (3,'c')]| 可得到
|([1,2,3],"abc")|.

許多情況下，我們不想要把兩兩對應的元素放到序對中，而是分別餵給一個二元運算子。
這時可用另一個相關函數 |zipWith|, 例：
|zipWith (+) [1,2,3] [4,5,6] = [5,7,9]|
函數 |zipWith| 可以這樣定義：
```spec
zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f = map (uncurry f) . zip {-"~~."-}
```

:::{.exlist}
:::{.exer #ex:zipWith-defn-zip}
用 |zipWith| 定義 |zip|.
:::
:::{.exans}
\Answer |zip = zipWith (,)|, 或 |zip = zipWith (\x y -> (x,y))|.
:::
:::

:::{.example #eg:positions}
試定義函數 |positions :: Char -> String -> List Int|, 使得
|positions z xs| 傳回 |z| 在 |xs| 中出現的所有位置。
例：|positions 'o' "hoola hooligans" = [1,2,7,8]|.
:::
:::{.answer}
一種可能寫法如下：
```haskell
positions z = map fst . filter ((==z) . snd) . zip [0..] {-"~~."-}
```
{.nobreak}我們用 |zip [0..]| 為輸入串列標上位置，用 |filter ((==z) . snd)|
取出第二個元素等於 |z| 的序對，最後用 |map fst| 取出所有位置。
注意函數合成與 currying 的使用。
:::

:::{.example #eg:positions-fst}
接續上例。如果我們僅想要 |z| 出現的第一個位置呢？我們可以定義：
```spec
pos :: Char -> String -> Int
pos z = head . positions z {-"~~."-}
```
{.nobreak}這是一個部分函數，|pos z xs| 傳回 |positions z xs| 的第一個結果。
如果 |z| 沒有出現，|positions z xs| 傳回 |[]|, |pos z xs|
會得到執行期錯誤。如果 |z| 出現在 |xs| 中，由於惰性求值，|pos|
得到第一個位置後 |positions| 便會停下，不會把串列整個產生。

如果我們希望 |pos| 在 |z| 沒有出現時傳回 |-1|, 可以這麼做：
```spec
pos :: Char -> String -> Int
pos z xs = case positions z xs of
            []      -> -1
            (i:is)  -> i {-"~~."-}
```
:::


## 全麥編程 {#sec:wholemeal}

讀者至此應已注意到本章採用的特殊編程風格。
一般說到串列，大家會先想到資料結構課程中常提到的連結串列(linked list)。
介紹連結串列的範例程式大多用迴圈或遞迴追蹤著指標，一個一個地處理串列中的元素。
在指令式語言中做關於陣列的操作時，也常用變數或指標指著「目前的」元素，
並在一個迴圈中將該變數逐次遞增或減。
總之，我們處理聚合型資料結構時，總是將其中元素一個個取出來處理。
但本章的做法不同：我們將整個串列視為一個整體，對整個串列做 |map|, |filter|, |dropWhile| 等動作，或將它和另一個串列整個 |zip| 起來...。

這種編程方式被稱作*全麥編程*(*wholemeal programming*)，\index{wholemeal programming 全麥編程}
第\@ref{sec:refs-basics}節中將解釋此詞的由來。
全麥編程的提倡者們認為：一個個地處理元素太瑣碎，而鼓勵我們拉遠些，
使用組件，以更抽象的方式組織程式的結構。

諸如 |map|, |filter|, |iterate|, |zipWith| 等等組件其實都是常見的編程模式。
它們可被視為*為了特定目的已先寫好的迴圈*。
拜高階函數與惰性求值之賜，這些組件能容易地被重用在許多不同脈絡中。
這麼做的好處之一是：諸如 |map|, |filter|, |zip| 等組件的意義清楚，
整個程式的意義也因此會比起自行在迴圈中一個個處理元素來得容易理解。
事實上，這麼做可以養成我們思考演算法的新習慣。
一些常見的編程模式現在是有名字的，我們*把編程模式抽象出來*了。
而如同第\@ref{ch:intro}章所述，抽象化是我們理解、掌握、操作事物的重要方法。
我們現在有了更多詞彙去理解、討論程式與演算法：
「這個演算法其實就是先做個 |map|，把結果 |concat| 起來，然後做 |filter|...」

在本書其他章節中我們也將看到：這些抽象化方便我們去操作、轉換程式。
具體說來，如果程式用這些組件拼湊成，我們對這些組件知道的性質都可用在我們的程式上。
例如，如果我們知道 |map f . map g = map (f . g)|，
當我們看到程式中有兩個相鄰的 |map|, 我們可用已知的性質把他們合併成一個 ---
這相當於合併兩個迴圈。或著我們可以把一個 |map| 拆成兩個，以方便後續的其他處理。
程式的建構方法使得程式含有更多資訊，使我們有更多可操作的空間。

全麥編程之所以成為可能，有賴程式語言的支援。
例如，高階函數使得我們能將與特定問題相關的部分
（如 |map f| 與 |filter p| 中的 |f| 與 |p|）抽象出來；
惰性求值使我們勇於使用大串列或無限串列作為中間值，不用擔心它們被不必要地真正算出。

此外，全麥編程也需要豐富的組件函式庫。設計良好的組件捕捉了常見的編程模式，
有了它們的幫忙，我們的程式可寫得簡潔明暸 ---
本章之中大部分的程式都是都是一行搞定的 ``one-liner''.
但，這些組件不可能窮舉所有的編程模式。我們仍會需要自行從頭寫些函數。
受到全麥編程影響，在自行寫函數時，我們也常會希望將它們寫得更通用些，
藉此發現常見的編程模式，設計出可重用的組件。

全麥編程能寫出多實用的程式？
第\@ref{sec:refs-basics}節中會提及其他學者嘗試過的，包含解密碼、解數獨在內的有趣例子。
在本節，我們則想示範一個小練習：由下至上的合併排序(merge sort)。
\index{merge sort 合併排序!bottom-up 由下至上}

{title="合併排序"} 假設我們已有一個函數 |merge' :: (List Int :* List Int) -> List Int|,
如果 |xs| 與 |ys| 已經排序好，|merge' (xs,ys)| 將它們合併為一個排序好的串列。%
^[之所以取名為 |merge'|，因為在第\@ref{sec:well-founded-induction}節中我們將使用一個類似且相關的函數 |merge :: List Int -> List Int -> List Int|.]
函數 |merge'| 可用第\@ref{sec:lexicographic-induction}節的方式歸納寫成，
也可使用將在第\todo{where}章提及的組件 |unfoldr| 做出。
我們如何用 |merge'| 將整個串列排序好呢？

一般書中較常提及由上至下的合併排序：
將輸入串列（或陣列）切成長度大致相等的兩半，分別排序，然後合併。
本節則以由下至上的方式試試看。
如果輸入串列為|[4,2,3,5,8,0,1,7]|，我們先把
每個元素都單獨變成串列，也就是變成|[[4],[2],[3],[5],[8],[0],[1],[7]]|。
然後把相鄰的串列兩兩合併：|[[2,4],[3,5],[8,0],[1,7]]|，
再兩兩合併成為 |[[2,3,4,5],[0,1,8,7]]|，
直到只剩下一個大串列為止。

如果我們定義兩個輔助函數：|wrap| 將一個元素包成一個串列，
|isSingle| 判斷一個串列是否只剩下一個元素，
::: {.multicols}
::: {.mcol width="0.4\\textwidth"}
```haskell
wrap :: a -> List a
wrap x = [x] {-"~~,"-}
```
:::
::: {.mcol width="0.4\\textwidth"}
```haskell
isSingle :: List a -> Bool
isSingle [x]  = True
isSingle xs   = False {-"~~."-}
```
:::
:::
{.nobreak}那麼上述的合併排序可以寫成：
```spec
msort = head . until isSingle mergeAdj . map wrap {-"~~."-}
```
{.nobreak}這幾乎只是把口語描述逐句翻譯：先把每個元素都包成串列，
反覆做 |mergeAdj| 直到只剩下一個大串列，然後將那個大串列取出來。

下一項工作是定義 |mergeAdj :: List (List Int) -> List (List Int)|,
其功能是將相鄰的串列兩兩合併。
如果我們能訂出一個函數 |adjs :: List a -> List (a :* a)|,
將相鄰的元素放在序對中，|mergeAdj| 就可以寫成：
```spec
mergeAdj = map merge' . adjs {-"~~."-}
```

但 |adjs| 該怎麼定義呢？
對大部分讀者來說，最自然的方式也許是用第\@ref{ch:induction}章將討論的歸納法。
但作為練習，我們姑且用現有的組件試試看。
先弄清楚我們對 |adjs| 的期待。
當 |xs = [x0,x1,x2,x3]|, 我們希望
|adjs xs = [(x0,x1),(x2,x3)]|.
但當 |xs| 有奇數個元素時，例如 |xs = [x0,x1,x2,x3,x4]|,
最後一個元素 |x4| 便落單了。
如果是為了合併排序，我們也許可以把 |x4| 和 |[]| 放在一起，
|adjs xs = [(x0,x1),(x2,x3),(x4,[])]|.
但為使 |adjs| 適用於更多的情況，也許我們應該讓它多拿一個參數，
當作落單的元素的配對。
因此我們把 |adjs| 的型別改為 |a -> List a -> List (a :* a)|,
希望 |adjs z xs = [(x0,x1),(x2,x3),(x4,z)]|.

我們試著看看這可如何辦到。

  * 首先，|zip xs (tail xs)| 可把 |xs| 的每個元素和其下一個放在序對中。
    例：當 |xs = [x0,x1,x2,x3,x4]| 時，
    |zip xs (tail xs)| 的值是 |[(x0,x1),| |(x1,x2),| |(x2,x3),| |(x3,x4)]|.
  * 如果我們為 |zip| 的第二個參數補上一個 |z|,
    成為 |zip xs (tail (xs ++ [z]))|，
    這可歸約為 |[(x0,x1),(x1,x2),(x2,x3),(x3,x4),(x4,z)]|。
  * 再將位置（由 |0| 算起）為奇數的元素丟棄，我們便得到原先希望的
    |[(x0,x1),(x2,x3),(x4,z)]| 了！

讀者可試試看當 |xs| 有偶數個元素時的情況。
總之，|adjs| 可定義成：
```haskell
adjs ::  a -> List a -> List (a :* a)
adjs z xs = everyother (zip xs (tail xs ++ [z])) {-"~~,"-}
```
{.nobreak}其中 |everyother ys| 把 |ys| 中位置為奇數的元素丟棄。

最後，考慮如何把串列中位置為奇數的元素丟棄。
一種做法是：一直從串列中丟掉頭兩個元素，直到串列用完：
```haskell
everyother :: List a -> List a
everyother = map head . takeWhile (not . null) . iterate (drop 2) {-"~~."-}
```

總而言之，由下至上的合併排序可寫成：
```haskell
msort :: List Int -> List Int
msort = head . until isSingle mergeAdj . map wrap {-"~~,"-}
```
{.nobreak}其中 |mergeAdj| 的定義是：
```haskell
mergeAdj :: List (List Int) -> List (List Int)
mergeAdj = map merge' . adjs [] {-"~~."-}
```


``` {.haskell .invisible}
merge' :: Ord a => (List a :* List a) -> List a
merge' ([],    ys)    = ys
merge' (x:xs,  [])    = x:xs
merge' (x:xs,  y:ys)  | x <= y     = x : merge' (xs, y:ys)
                      | otherwise  = y : merge' (x:xs, ys) {-"~~."-}
```

如果我們想看到合併排序完成前的每一步驟，可將 |msort| 中
（以 |iterate| 與 |dropWhile| 定義出）的 |until|
改為 |iterate| 與 |takeWhile|:
```haskell
msortSteps :: List Int -> List (List (List Int))
msortSteps = takeWhile (not . isSingle) . iterate mergeAdj . map wrap {-"~~."-}
```
{.nobreak}例如，|msortSteps [9,2,5,3,6,4,7,0,5,1,8,2,3,1]| 可得到
```spec
[  [[9],[2],[5],[3],[6],[4],[7],[0],[5],[1],[8],[2],[3],[1]],
   [[2,9],[3,5],[4,6],[0,7],[1,5],[2,8],[1,3]],
   [[2,3,5,9],[0,4,6,7],[1,2,5,8],[1,3]],
   [[0,2,3,4,5,6,7,9],[1,1,2,3,5,8]]] {-"~~."-}
```
{.nobreak}最後兩個串列合併為 |[0,1,1,2,2,3,3,4,5,5,6,7,8,9]|，即為 |msort| 的結果。


## 自訂資料型別 {#sec:user-defined-data}

本章目前為止給讀者看到的 |data| 定義其實都是 Haskell 已內建的型別。
使用者也可自己定義新資料型別。
例如，我們可能定義一個新型別表達四個方向：
```spec
data Direction = North | East | South | West {-"~~,"-}
```
或著定義一個表示顏色的型別，用三個浮點數表達紅、綠、藍的比例：
```haskell
data RGBColor = RGB Float Float Float {-"~~,"-}
```
例：土耳其藍(turquoise)可寫成 |RGB 0.25 0.875 0.8125|.
下列函數則降低一個顏色的彩度：
^[這是一個簡便的做法：算出該顏色的灰度 |gr|,
然後計算每個原色與該灰度的線性內插。
更準確的作法應將 RGB 轉成 HSV，以後者調整飽和度。]
```haskell
desaturate :: Float -> RGBColor -> RGBColor
desaturate p (RGB r g b) =
    RGB  (r +. p *. (gr -. r)) (g +. p *. (gr -. g)) (b +. p *. (gr -. b)) {-"~~,"-}
  where gr = r *. 0.299 +. g *. 0.587 +. b *. 0.144 {-"~~."-}
```

我們也可定義如 |List| 一樣的遞迴資料型別。
例如，資料結構中可能談到兩種二元樹狀結構，一種僅在內部節點有標示（稱作 internally labelled），另一種僅在葉節點有表示（稱作 externally labelled）。
這兩種二元樹可分別表示如下：
```haskell
data ITree a  = Null | Node a (ITree a) (ITree a) {-"~~,"-}
data ETree a  = Tip a | Bin (ETree a) (ETree a) {-"~~."-}
```
``` {.haskell .invisible}
deriving instance Eq a => Eq (ITree a)
deriving instance Eq a => Eq (ETree a)
deriving instance Show a => Show (ITree a)
deriving instance Show a => Show (ETree a)
```

怎麼編寫這種資料結構上的程式呢？我們將在下一章中說到。

## 參考資料 {#sec:refs-basics}

本章中的許多想法取自 @Bird:98:Introduction ，該書是我相當推薦的 Haskell 教材。

::: {.infobox title="Haskell 為何叫 Haskell?"}
1980 年代中期，程式語言學者們已各自開發出了許多個語法、語意類似但卻稍有不同、大都只在出生機構被使用的惰性純函數語言。沒有一個語言取得壓倒性的優勢。
為溝通方便、以及為了讓整個領域能走向下一步，大家有了該設計個統合、共通的惰性純函數語言的共識。
1988年一月，新語言設計小組在耶魯大學開會，眾多討論項目中包括幫語言取個名字。
以下軼事節錄自 @Hudak:07:Being .

當天被提出的選項包括 Haskell, Vivaldi, Mozart, CFL (Common Functional Language), Curry, Frege, Peano, Nice, Fun, Light...等等。最後經程序選出的名字是 ``Curry'', 紀念邏輯學家 Haskell B. Curry --- 他在組件邏輯(combinatorial logic)、Curry-Howard 同構等領域的研究一直深遠影響函數語言學界。

但當天晚上就有人覺得這名字會招惹太多雙關語笑話。除了咖哩之外，小組成員覺得實在不行的是：TIM (three instruction machine) 是函數語言用的一種抽象機器，但 Tim Curry 則成了電影洛基恐怖秀（Rocky Horror Picture Show, 1975）的男主角。

於是新語言的名字就改成 Haskell 了。

小組成員 Paul Hudak 和 David Wise 寫信給 Curry 的遺孀 Virginia Curry，徵求她的同意。Hudak 後來親自登門拜訪，Virginia Curry 和他聊了之前的訪客（包含 Church 與 Kleene）的故事；後來她也去聽了 Hudak 關於 Haskell （語言）的演講，表現得十分友善。臨別前，她說：「其實呀，Haskell 一直都不喜歡他的名字。」
:::

{title="Currying"}
Moses [@Schonfinkel:24:Uber] 提出多參數函數可用單參數函數表達。
Haskell Curry 在許多著作中（例：@Curry:80:Some ）使用 currying，
但當時並沒有 currying 一詞。
為何此概念最後會以 Curry 命名呢？
David A. Turner （Haskell 語言的前身之一 Miranda 的設計人）
在一次網路討論 [@Sankar:97:Currying] 中表示 currying 一詞由
Christopher Strachey 取名，於 1967 年前後使用在其上課資料中。
這種說法目前廣被大家接受，但我目前尚未找可佐證的上課資料。
相反地，@Strachey:67:Fundamental 之中明確表示他認為 currying
的概念是由 Sch\"{o}nfinkel 發明的，並稱之為「Sch\"{o}nfinkel 的裝置」。
^[原文：``There is a device originated by Sch\"{o}nfinkel,
for reducing operators with several operands to the successive application of single operand operators.'']
但 currying 的想法可追溯得比 Sch\"{o}nfinkel 或 Curry 都早。
F. L. Gottlob Frege 1891 年的
\"{U}ber Funktion und Begriff (英譯 Function and Concept)
[@Frege:60:Function] 結尾幾頁的概念即是 currying.

{title="全麥編程"}
「全麥編程」一詞由牛津大學 Geraint Jones 取名，由來可能是模仿健康食物的說詞。
如 @Bird:10:Pearls[第19章] 便寫道，「全麥編程好處多多，可預防『索引症』(indexitis)，鼓勵合法的程式建構。」
在該章之中，Richard Bird 以大量使用串列組件函數的全麥編程為起點，
推導出能相當迅速地解數獨的程式。
@Hinze:09:La 以全麥編程為工具，示範了河內塔問題(Tower of Hanoi)
的許多性質，以及其與謝爾賓斯基(Sierpi\'{n}ski)三角形的關係。
其中寫道「函數語言擅長全麥編程。這個詞彙由 Geraint Jones 命名。
全麥編程意謂由大處去想：處理整個串列，而不是一連串的元素；發展出整個解答的空間，而不是個別的解答；想像整個圖，而不是單一的路徑。對於已知的問題，全麥編程常給我們新洞察與新觀點。」
@Hutton:16:Programming[第五章] 則以編、解密碼為例。
*凱撒加密*(*Caesar cipher*)為一種簡單的加密方式：
將明文中的每個字母都往前或後偏移固定的量，例如當偏移量為 |2| 時， |'a'| 變成 |'c'|，
|'b'| 變成 |'d'| ... 一種解凱撒密碼的有效方式是計算密文中每個字母的分佈，和一般英文文章中的平均字母分佈做比較，藉以猜出偏移量。Graham Hutton 在書中示範如何用組件函數、完全不用遞迴地寫出編碼與解碼程式。以上都是相當值得一看的例子。

{title="LISP 的串列"}
誕生於 1958 年的 LISP \index{LISP} 是目前仍被使用的高階程式語言中歷史第二悠久的 --- 最早的是 FORTRAN.
但 LISP 與 FORTRAN 是風格截然不同的語言。
雖然具有含副作用的指令，LISP 仍被認為是函數語言的先驅。

LISP 為「串列處理(list processing)」的縮寫。
但事實上，LISP 中的聚合資料結構「|S| 算式 (S-expression)」不只可用來表達串列。
|CONS| 函數做出的是一個序對，
其中第一個元素被稱作 |CAR| (contents of the address part of register),
第二個稱作 |CDR| (contents of the decrement part of register).
如果 |CDR| 的部分仍是一個 |CONS| 做出的序對，或是特殊值 |NIL|,
整個結構表達的就是一個串列。
|S| 算式也可用來做出二元樹、語法樹... 等等。
Haskell 串列的建構元 |[]| 可唸成 ``nil'', |(:)| 唸成 ``cons'', 這兩個詞彙都從 LISP 而來。

在前幾波人工智慧熱潮時，大家認為符號與邏輯的處理是人工智慧的基礎。
但早期的程式語言大多針對數值運算而設計，會處理串列的 LISP 便被視為最適合做符號處理的語言 ---「人工智慧用的語言」。
另一個被視為「人工智慧專用語言」的是奠基於述語邏輯與歸結(resolution)
\index{logic programming 邏輯編程!resolution 歸結}
的 PROLOG.
今日的人工智慧技術以神經網路為基礎，「人工智慧專用語言」的頭銜則給了 Python。
