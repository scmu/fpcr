``` {.haskell .invisible}
{-# LANGUAGE TypeOperators #-}
module Chapters.Induction where

import Prelude ()
import Control.Arrow ((***))
import Common.MiniPrelude hiding (exp, length, take, drop, gcd)
import Chapters.Basics (ETree(..), ITree(..))
```

# 歸納定義與證明 {#ch:induction}

「全麥編程」的觀念鼓勵我們以小組件組織出大程式。
但這些個別組件該如何實作呢？或著，沒有合用的組件時該怎麼辦？
我們可以回到更基礎的層次，用*遞迴*(recursion)\index{recursion 遞迴}定義它們。
「遞迴」意指一個值的定義又用到它本身，是數學中常見的定義方式。
在早期的編程教材中，遞迴常被視為艱澀、難懂、進階的主題。
但在函數程設中，遞迴是唯一可使程式不定次數地重複一項計算的方法。
一旦跨過了門檻，遞迴其實是個很清晰、簡潔地描述事情的方式。

對於遞迴，許多初學者一方面不習慣、覺得如此構思程式很違反「直覺」，另一方面也納悶：以自己定義自己，到底是什麼意思？
這兩個難處其實都談到了好問題。
對於前者，我們希望發展一些引導我們構思遞迴程式的思路；希望有了這些依據，能使寫遞迴程式變得直覺而自然。
關於後者，其實並非所有遞迴定義都有「意思」 --- 有些「不好」的遞迴並沒有定義出東西。我們討論遞迴的意義時必須限定在「好」的、有意義的程式上。最好有些方式確保我們寫出的遞迴定義是好的。

在本章我們將討論一種型式較單純的遞迴：*歸納*(induction)\index{induction 歸納}。
對上述兩個問題，本章的回應是：先有歸納定義出的資料結構，再依附著該資料結構撰寫歸納定義的程式，是一種思考、解決程式問題的好方法，也是一種理解遞迴程式的方式。
此外，依循這種方法也能確保該定義是「好」的。
我們將從數學歸納法出發，發現歸納程式與數學歸納法的相似性 --- 寫程式和證明其實是很相似的活動。

本書以 Haskell 為學習工具，但在之後的幾章，我們僅使用 Haskell 的一小部分。
Haskell 支援無限大的資料結構，也允許我們寫出不會終止的程式。
但我們將假設所有資料結構都是有限的（除非特別指明），所有函數皆會好好終止（也就是說函數都是「*全函數*(total function)」\index{total function 全函數}--- 對每一個值，都會好好地算出一個結果，不會永遠算下去，也不會丟回一個錯誤）。這麼做的理由將在本章解釋。

## 數學歸納法 {#sec:math-induction}

在討論怎麼寫程式之前，我們得先複習一下*數學歸納法* --- 晚點我們就會明白理由。
回顧：*自然數*\index{natural number 自然數}在此指的是|0, 1, 2...| 等所有非負整數。
^[有些數學派別的「自然數」是從 |1| 算起的。計算科學中則通常習慣以 |0| 起算。]
自然數有無限多個，但每個自然數都是有限大的。
自然數的型別記為 |Nat|.
若|a|是一個型別, |a|之上的*述語*(predicate)\index{predicate 述語}可想成型別為|a -> Bool|的函數，常用來表示某性質對某特定的|a|是否成立。
自然數上的述語便是|Nat -> Bool|。
數學歸納法可用來證明某性質對所有自然數都成立：

> 給定述語|P :: Nat -> Bool|. 若
>
>   1. |P| 對 |0| 成立，並且
>   2. 若 |P| 對 |n| 成立，|P| 對 |1+n| 亦成立，
>
> 我們可得知 |P| 對所有自然數皆成立。

為何上述的論證是對的？我們在\@ref{sec:induction-set-theory}節將提供一個解釋。但此處我們可以提供一個和程式設計較接近的理解方式。自然數可被想成如下的一個資料結構：
```spec
  data Nat = Zero | Suc Nat {-"~~."-}
```
這行定義有幾種讀解法，目前我們考慮其中一種 --- 該定義告訴我們：

  1. |Zero| 的型別是 |Nat|;
  2. 如果 |n| 的型別是 |Nat|, |Suc n| 的型別也是 |Nat|;
  3. 此外，沒有其他型別是 |Nat| 的東西。

{.nobreak}這種定義方式稱作*歸納定義*(inductive definition)。
其中「沒有其他型別是 |Nat| 的東西」一句話很重要 ---
這意味著任一個自然數只可能是 |Zero|，或是另一個自然數加一，沒有別的可能。
任一個自然數都是這麼做出來的：由 |Zero| 開始，套上*有限*個 |Suc|。
反過來說，給任意一個自然數，我們將包覆其外的 |Suc| 一層層拆掉，在有限時間內一定會碰到 |Zero|.
有人主張將 inductive definition 翻譯為*迭構定義*，著重在從基底（此處為 |Zero|）開始，一層層堆積上去（此處為套上 |Suc|）的概念。

本書中，我們把自然數的 |Zero| 寫成粗體，表明它是資料建構元；把 |Suc| 的加號寫得小些並和 $\mathbf{1}$ 放得很近，以強調「加一」是資料建構元、是一個不可分割的動作（和我們之後將介紹的一般自然數加法|(+)|不同）。
數字 |2| 其實是 |Suc (Suc Zero)| 的簡寫, |3| 其實是 |Suc (Suc (Suc Zero))| 的簡寫。

歸納定義出的資料型別允許我們做*歸納證明*。
由於 |P| 是 |Nat| 到 |Bool| 的函數，「|P| 對 |0| 成立」可記為 |P Zero|，「若 |P| 對 |n| 成立，|P| 對 |1+n| 亦成立」可記為 |P (Suc n) <== P n|。
^[|P <== Q| 意思是「若 |Q| 則 |P|」。依此順序寫，有「為證明 |P|，我們想辦法讓 |Q| 成立」的感覺。許多人不習慣由右到左的箭頭，但不論數學上或日常生活中，這都是常使用的論證思考方向。]
我們假設兩者都已被證明，用它們證明 |P 3|：
```spec
     P (Suc (Suc (Suc Zero)))
<==    {- 因 |P (Suc n) <== P n| -}
     P (Suc (Suc Zero))
<==    {- 因 |P (Suc n) <== P n| -}
     P (Suc Zero)
<==    {- 因 |P (Suc n) <== P n| -}
     P Zero {-"~~."-}
```
{.nobreak}第一步中，我們希望 |P (Suc (Suc (Suc Zero)))| 成立，根據 |P (Suc n) <== P n|, 只要 |P (Suc (Suc Zero))| 即可。第二步中，我們希望 |P (Suc (Suc Zero))| 成立，同樣根據|P (Suc n) <== P n|，只要 |P (Suc Zero)| 成立即可... 最後，只要 |P Zero| 成立，|P (Suc Zero)| 即成立，但 |P Zero| 是已知的。因此我們已論證出 |P 3| 成立！

由上述推演中，我們發現：數學歸納法的兩個前提 |P Zero| 與 |P (Suc n) <== P n| 給了我們一個*對任一個自然數|m|, 生成一個 |P m| 之證明*的方法。
這是由於自然數本就是一個歸納定義出的資料型別：任一個自然數 |m| 都是有限個 |Suc| 套在 |Zero| 之上的結果，因此，只要反覆用 |P (Suc n) <== P n| 拆，總有碰到 |P Zero| 的一天。
既然對任何 |m|, 都做得出一個 |P m| 的證明，我們就可安心相信 |P| 對任何自然數都成立了。

為了之後討論方便，我們將前述的數學歸納法寫得更形式化些：
```{.equation title="自然數上之歸納法：" #eq:induction-on-Nat}
|(forall n . P n) {-"~"-}<== {-"~"-} P Zero && (forall n . P (Suc n) <== P n) {-"~~."-}|
```
{.nobreak}這只是把之前的文字描述改寫成二階邏輯，但可清楚看出：給定 |P|, 我們希望證明它對所有自然數都成立，只需要提供 |P Zero| 和 |P (Suc n) <== P n| 兩個證明。
其中 |P Zero| 是確定 |P| 對 |0| 成立的*基底* (base case)，\index{induction 歸納!base case 基底}
|P (Suc n) <== P n| 則被稱作*歸納步驟*(inductive step)：\index{induction 歸納!inductive step 歸納步驟}
在*假設 |P n| 成立的前提下，想辦法「多做一步」，論證 |P (Suc n)| 也成立*。餘下的就可交給數學歸納法這個架構了。

## 自然數上之歸納定義 {#sec:induction-on-Nat}

數學歸納法和編程有什麼關係呢？考慮一個例子：給定 |b, n :: Nat|, 我們希望寫個函數 |exp| 計算乘冪，使得 |exp b n = {-"\Varid{b}^{\Varid{n}}"-}|. 我們先把型別寫下：
```spec
exp :: Nat -> Nat -> Nat
exp b n = ?
```
{.nobreak}問號部分該怎麼寫？沒有其他線索很難進行，因此我們回想：|n| 是自然數，而任何自然數只可能是 |Zero| 或 |Suc| 做出的。我們便分成這兩個狀況考慮吧：
```spec
exp :: Nat -> Nat -> Nat
exp b Zero     = ?
exp b (Suc n)  = ?
```
{.nobreak}其中，|exp b Zero| 較簡單：顯然應該是 $\Varid{b}^0 = 1$. 至於 |exp b (Suc n)| 的右手邊該怎麼寫？似乎很難一步定出來。
但*假設 |exp b n| 已經順利算出了$\Varid{b}^{\Varid{n}}$*, 由於 $\Varid{b}^{1+\Varid{n}} = \Varid{b} \times \Varid{b}^{\Varid{n}}$, |exp b (Suc n)| 與之的關係可寫成：
```spec
exp b (Suc n) = b * exp b n {-"~~."-}
```
{.nobreak}如此一來我們便完成了一個計算乘冪的程式：
```haskell
exp :: Nat -> Nat -> Nat
exp b Zero     = 1
exp b (Suc n)  = b *: exp b n {-"~~."-}
```

::: {.infobox title="Haskell v.s Math"}
很不幸地，Haskell 並不接受\@ref{sec:induction-on-Nat}節中|exp|的定義。

首先，Haskell 並沒有獨立的自然數型別。我們可自己定（並將其宣告為 |Num| 類別的一員），或著直接使用 Haskell 內建的 |Int| 型別。
其次，Haskell 原本允許我們在定義的左手邊寫 |exp b (n+1)| ，但這套稱作``|n+k| pattern'' 的語法已在 Haskell 2010 中被移除。目前我們得將 |exp| 寫成：
```spec
exp :: Int -> Int -> Int
exp b 0  = 1
exp b n  = b * exp b (n-1) {-"~~."-}
```
{.nobreak}|n+k| pattern 曾引起激烈討論。支持者主要著眼於它在教學上的方便：這方便我們討論數學歸納法、做證明、並讓我們更明顯地看出自然數與串列的相似性。
反對者則批評它與 type class 的衝突。後來由反方勝出。

有些 Haskell 教科書堅持書中出現的程式碼須是能在一個字一個字地鍵入電腦後即可執行的。
本書的定位並非 Haskell 教材，而是函數編程概念的入門書。
為此目的，我們希望選擇適合清晰表達概念、易於操作、演算、證明的符號。
而一個實用目的的語言得在許多設計上妥協尋求平衡，基於種種考量，往往得犧牲符號的簡潔與便利性（這點我們完全能理解）。
因此本書中的程式語法偶爾會和 Haskell 語法有所不同。
我們會盡量指明這些不同處，使讀者知道如何將本書中的程式轉換成現下的 Haskell 語法。
:::

回顧一下剛剛的思路：我們難以一步登天地對任何 |n| 寫出 |exp b n|, 但我們提供 |exp b Zero| 該有的值，並在假設 |exp b n| 已算出該有的值的前提下，試著做一點加工、多算那一步，想法做出 |exp b (Suc n)| 該有的值。
這和前述的數學歸納法是一樣的！
*寫歸納程式和做歸納證明是很類似的行為。*
使用數學歸納法證明 |P| 需要提供一個基底 |P 0| 和歸納步驟 |P (Suc n) <== P n|.
歸納定義程式也一樣。
在 |exp b n| 的定義中，基底是 |exp b Zero|，歸納步驟則是由 |exp b n| 想法變出 |exp b (Suc n)|.
有這兩個元件，我們便有了一個*對任何自然數 |n|, 保證算出 |exp b n| 的方法*。作為例子，我們看看 |exp 2 3| 是怎麼被算出來的：
```spec
   exp 2 (Suc (Suc (Suc Zero)))
=    {- |exp| 之歸納步驟 -}
   2 * exp (Suc (Suc Zero))
=    {- |exp| 之歸納步驟 -}
   2 * 2 * exp (Suc Zero)
=    {- |exp| 之歸納步驟 -}
   2 * 2 * 2 * exp Zero
=    {- |exp| 之基底 -}
   2 * 2 * 2 * 1 {-"~~."-}
```
{.nobreak}第一步中，要算出 |exp 2 (Suc (Suc (Suc Zero)))|, 我們得先算出 |exp (Suc (Suc Zero))|. 要算出後者，在第二步中我們得先算出 |exp (Suc Zero)|... 直到我們碰到 |exp b Zero|.

{title="自然數上的歸納定義"}
我們將 |b| 固定，稍微抽象一點地看 |exp b :: Nat -> Nat| 這個函數。該定義符合這樣的模式：
```spec
f :: Nat -> a
f Zero     = e
f (Suc n)  = ... f n ... {-"~~."-}
```
{.nobreak}這類函數的輸入是 |Nat|，其定義中 |f (Suc n)| 的狀況以 |f n| 定出，此外沒有其他對 |f| 的呼叫。若一個函數符合這樣的模式，我們說它是*在自然數上歸納定義*出的，其中 |f Zero| 那條稱作其基底，|f (Suc n)| 那條稱作其歸納步驟。我們日後將看到的許多程式都符合這個模式。

數學上，若一個函數能為其值域內的每個值都找到一個輸出，我們說它是個全函數(total function)，否則是部分函數(partial function).
計算上，當我們說 |f| 是一個全函數，意謂只要 |x| 型別正確並可算出值，|f x| 便能終止並算出一個值，不會永久跑下去，也不會丟出錯誤。

如前所述的、在自然數上歸納定義的 |f| 會是全函數嗎？首先，任何自然數都可拆成 |Zero| 或是 |Suc n|，而這兩個情況已被 |f| 的兩行定義涵括，不會出現漏失的錯誤。其次，|f| 每次呼叫自己，其參數都少了一層 |Suc|. 長此以往，不論輸入多大，總有一天會遇到基底 |f Zero| ---
因為任何自然數都是從 |Zero| 開始，套上有限個 |Suc|.
只要基底狀況的 |e| 以及在歸納步驟中 |f n| 前後的計算都正常終止，對任何輸入，|f| 都會正常終止。因此 |f| 是個全函數。

「程式會終止」是很重要的性質，我們之後會常談到。
在本書目前為止示範的編程方法中，「一個函數若呼叫自己，只能給它更小的參數」是個單純但重要的規範
（例如 |f (Suc n)| 的右手邊可以有 |f n|, 不能有 |f (Suc n)| 或 |f (Suc (Suc n))|）。
操作上這確保程式會終止，而在第 \todo{where?} 章之中，我們將提到這也確保該遞迴定義是「好」的、有意義的。

順便一提：在 |f (Suc n)| 的右手邊中，|f n| 可以出現不只一次 ---
因為 |... f n ... f n ...| 可看成
|(\x -> ... x ...x ...) (f n)|.
在 |f n| 的前後 |...| 的部分可以出現 |n| --- 將在第\@pageref{ex:factorial}頁中介紹的階層函數就是一個這樣的例子。
有些情況下我們不允許 |n| 出現在 |...| 中，此時會額外說明。

{title="乘法、加法"} 我們多看一些歸納定義的例子。在 |exp| 中我們用到乘法，但假若我們的程式語言中只有加法、沒有乘法呢？我們可自己定定看：
```spec
(*) :: Nat -> Nat -> Nat
m * n = ?
```
{.nobreak}若不用組件，我們目前會的寫程式方法只有歸納法，也只有這招可試試看了。
但，|(*)| 有兩個參數，我們該把 |(m *) :: Nat -> Nat| 視為一個函數，分別考慮 |n| 是 |Zero| 或 |Suc ...| 的情況，還是把
|(* n) :: Nat -> Nat| 視為一個函數，考慮 |m| 是 |Zero| 或 |Suc ...| 的情況？答案是兩者皆可，並無根本性的差異。只是現在我們做的選擇會影響到之後與 |(*)| 相關的證明怎麼寫(見第\@ref{sec:inductive-proof-on-Nat}節)。本書中的習慣是拆左手邊的參數，因此我們考慮以下兩種情況。
```spec
(*) :: Nat -> Nat -> Nat
Zero     * n  = ?
(Suc m)  * n  = ... m * n ....
```
{.nobreak}基底狀況中，|Zero * n| 的合理結果應是 |Zero|.
歸納步驟中，我們得想法算出 |(Suc m) * n|, 但我們可假設 |m * n| 已經算出了。
稍作思考後，讀者應可同意以下的做法：
```spec
(*) :: Nat -> Nat -> Nat
Zero     * n  = Zero
(Suc m)  * n  = n + (m * n) {-"~~,"-}
```
{.nobreak}如果已有 |m * n|，多做一個 |(n+)|, 就可得到 |(Suc m) * n|了。

如果我們的程式語言中連加法都沒有呢？加法可看成連續地做 |Suc|:
```spec
(+) :: Nat -> Nat -> Nat
Zero     + n  = n
(Suc m)  + n  = Suc (m + n) {-"~~."-}
```
{.nobreak}此處 |(+)| 是我們定義的、可將任意兩個自然數相加的加法，而 |Suc| 只做「加一」，是基本的資料建構元。
為求一致，我們同樣在左邊的參數上做歸納。
基底狀況中，|Zero + n| 只應是 |n|. 想計算 |(Suc m) + n|, 先假設 |m+n| 已經算出，再多套一個 |Suc|. 不難看出 |m + n| 是把 |n| 當做基底，在外面套上 |m| 個 |Suc| 的結果。
^[「這樣做不是很慢嗎？」是的。本章的自然數表示法，以及其引申出的運算元都不應看作有效率的實作，而是理論工具。了解加法與乘法可這樣看待後，許多其相關性質都可依此推導出來。]

## 自然數上之歸納證明 {#sec:inductive-proof-on-Nat}

上一節中我們定出了函數 |exp|。如果定義正確，|exp b n| 算的應是 $\Varid{b}^\Varid{n}$.
例如，我們知道 $\Varid{b}^\Varid{m+n} = \Varid{b}^\Varid{m} \times \Varid{b}^\Varid{n}$. 我們定出的函數 |exp| 是否真有此性質呢？

::: {.theorem #thm:exp-plus-times}
  對任何 |b, m, n :: Nat|, |exp b (m + n) = exp b m * exp b n|.
:::
{.nobreak}我們試著證明定理\@ref{thm:exp-plus-times}。數學歸納法是我們目前唯一的工具，
而要使用它，第一個問題是：該用 |b|, |m|, 或 |n| 的哪一個來做歸納呢（意即把哪一個拆解）？

觀察定理\@ref{thm:exp-plus-times}中待證明式的等號兩邊，並參照 |exp|, |(+)|, 與 |(*)|的定義。
等號左手邊的 |exp b (m + n)| 之中，化簡 |exp b| 前得知道 |m + n| 究竟是 |Zero| 還是 |Suc k|。
而根據 |(+)| 的定義，化簡 |m + n| 前需知道 |m| 究竟是 |Zero| 還是 |Suc k|.
再看右手邊，根據 |(*)| 的定義，要化簡 |exp b m * exp b n| 得先化簡 |exp b m|, 而後者也得知道 |m| 是什麼。對兩邊的分析都指向：我們應針對 |m| 做歸納！

策略擬定後，我們便試試看吧！

::: {.proof title="證明定理 thm:exp-plus-times"}
欲證明 |exp b (m + n) = exp b m * exp b n|, 我們在 |m| 之上做歸納。
|m| 要不就是 |Zero|, 要不就是 |Suc k|.

{.noindent}**情況** |m := Zero|. 此時需證明 |exp b (Zero + n) = exp b Zero * exp b n|. 推論如下：
```{.haskell .invisible}
expPlusTimesP0 b n =
```
```haskell
   exp b (Zero +: n)
 ===    {- |(+)| 之定義 -}
   exp b n
 ===    {- 因 |1 * k = k| -}
   1 *: exp b n
 ===    {- |exp| 之定義 -}
   exp b Zero *: exp b n {-"~~."-}
```

{.noindent}**情況** |m := Suc m|. 此時需證明 |exp b ((Suc m) + n) = exp b (Suc m) * exp b n|, 但可假設 |exp b (m + n) = exp b m * exp b n| 已成立。推論如下：
```{.haskell .invisible}
expPlusTimesP1 b m n =
```
```haskell
   exp b ((Suc m) +: n)
 ===    {- |(+)| 之定義 -}
   exp b (Suc (m +: n))
 ===    {- |exp| 之定義 -}
   b *: exp b (m +: n)
 ===    {- 歸納假設 -}
   b *: (exp b m *: exp b n)
 ===    {- |(*)| 之結合律 -}
   (b *: exp b m) *: exp b n
 ===    {- |exp| 之定義 -}
   exp b (Suc m) *: exp b n {-"~~."-}
```
:::

對這個證明，讀者是否有所懷疑？最大的疑問可能在「假設 |exp b (m + n) = exp b m * exp b n| 成立」這句上。這不就是我們要證明的性質嗎？在證明中假設它成立，似乎是用該性質自己在證明自己。這是可以的嗎？

為清楚說明，我們回顧一下第\@ref{sec:math-induction}節中的數學歸納法（並把區域識別字改為 |k| 以避免混淆）：
```{.equation title="自然數上之歸納法："}
  |(forall k . P k) {-"~"-}<== {-"~"-} P Zero && (forall k . P (Suc k) <== P k) {-"~~."-}|
```
{.nobreak}證明\@ref{thm:exp-plus-times}欲證的是 |exp b (m + n) = exp b m * exp b n|，並在 |m| 上做歸納。
更精確地說，就是選用了下述的 |P|:
^[在程式推導圈子中，|(<=>)| 常用來代表「只用在真假值上、且滿足結合律的等號」。本書中使用 |(<=>)| 以和 |(=)| 做區分。]
```spec
P m <=> (exp b (m + n) = exp b m * exp b n) {-"~~,"-}
```
{.nobreak}在證明中改變的是 |m|，而 |b| 與 |n| 是固定的。數學歸納法可證明 |(forall m . P m)|, 展開後正是 |(forall m . exp b (m + n) = exp b m * exp b n)|. 而根據數學歸納法，我們需提供 |P Zero| 與 |(forall m . P (Suc m) <== P m)| 的證明。

證明\@ref{thm:exp-plus-times}中「{\bf 情況} |m := Zero|」的部分，就是 |P Zero| 的證明。
而「{\bf 情況} |m := Suc m|」則是 |(forall m . P (Suc m) <== P m)| 的證明。
「假設 |exp b (m + n) = exp b m * exp b n| 成立」指的是假設 |P m| 成立，我們在此前提之下試圖證明 |P (Suc m)|.
因此，證明 \@ref{thm:exp-plus-times} 並沒有「用該性質自己證明自己」。
我們是以一個比較小的結果（|P m|）證明稍大一點的結果（|P (Suc m)|）。
就如同我們寫歸納程式時，假設 |f n| 已經算出，試著用它定出 |f (Suc n)|.

在證明之中，如 |P m| 這種在歸納步驟假設成立的性質被稱作*歸納假設*(induction hypothesis)。\index{induction 歸納!induction hypothesis 歸納假設}

{title="程式與證明"} 證明\@ref{thm:exp-plus-times}還有一些能啟發我們之處。方才，我們看到 |exp b (m + n) = exp b m * exp b n|， 決定以數學歸納法證明，但接下來怎麼著手？怎麼選定在哪個變數上做歸納？

答案是：分析該式中程式的行為。程式怎麼拆其參數，我們在證明中就怎麼拆。
我們試圖證明某些程式的性質，但程式本身便提供了證明可怎麼進行的提示。
「使證明的結構符合程式的結構」是許多證明的秘訣。
並非所有證明都可以如此完成，但本原則在許多情況下適用。

再看看 |exp|, |(+)|, |(*)| 等函數的定義。
為何他們都分出了兩個情況：|Zero| 與 |Suc n|, 並且 |Suc n| 的情況使用到該函數對於 |n| 的值？
因為自然數的資料型別是這麼定的！
自然數只可能是|Zero| 或 |Suc n|，而後者是由 |n| 做出來的。
因此程式也如此寫。程式的結構依循與其處理的資料型別之結構。

資料、程式、與證明原來有著這樣的關係：*證明的結構依循著程式的結構，而程式的結構又依循著資料型別的結構*。歸納定義出了一個型別後，自然知道怎麼在上面寫歸納程式；歸納程式有了，自然知道如何做關於這些程式的歸納證明。一切由定義資料結構開始。掌握這個原則，大部分的證明就不是難事。

{title="讓符號為你工作"} 再考慮證明\@ref{thm:exp-plus-times}中的狀況|m := Suc m|. 假想由你做這個證明，由第一行 |exp b ((Suc m) + n)| 開始。接下來該怎麼進行？

既然我們已經打定主意用數學歸納法，在證明的某處必定會使用|exp b (m + n) = exp b m * exp b n|這個歸納假設。
因此，證明前幾行的目的便是想辦法將 |exp b ((Suc m) + n)| 中的 |Suc| 往外提，將 |exp b| 往內側推，使得式子中出現 |exp b (m + n)|。一旦成功，就可運用歸納假設，將其改寫成 |exp b m * exp b n|！
接下的就是機械化地收尾、將式子整理成 |exp b (Suc m) * exp b n| 了。

這呼應到第\@ref{sec:let-symbols-work}節所說的「讓符號為你工作」。
光從語意上想，我們不易理解為何 |exp b ((Suc m) + n)| 能夠等於 |exp b (Suc m) * exp b n|. 但符號給我們線索。
我們可觀察式子的結構，暫時不去想語意；
我們的目標是操作、移動這些符號，將它們轉換成可使用歸納假設的形式。
因此，接下來的演算推導便有所依據而非盲目進行：已知目標是把某符號往外提或往內推，
我們就可尋找、使用可達到此目的的規則。
這些規則包括已知函數的定義、或諸如分配律、遞移律、結合律等等數學性質。
若很明顯地缺了一個想要的性質，也許可以把它當作引理另外證證看。
符號幫助我們，使我們的思考清晰而有方向。

:::{.exlist}
:::{.exer #ex:proof-no-induction}
證明 |1 * k = k|. 這個證明並不需要歸納。
:::
:::{.exer #ex:add-associative}
證明 |(+)| 之結合律: |m + (n + k) = (m + n) + k|. 此證明中你使用的述語是什麼？
:::
:::{.exer #ex:add-right-id}
證明 |k + 1 = k|. 你需要使用歸納法嗎？用什麼述語？
:::
:::

最後，說到自然數上的歸納定義，似乎不得不提*階層*(factorial)。用非正式的寫法，|fact n = n * (n-1) * (n-2) * ... * 1|.
\index{factorial 階層}
\label{ex:factorial}
形式化的定義如下：
```haskell
fact :: Nat -> Nat
fact Zero     = 1
fact (Suc n)  = (Suc n) *: fact n {-"~~."-}
```
{.nobreak}我們在定理 \@ref{thm:length-perms} 中將會談到階層與排列的關係。


## 串列與其歸納定義 {#sec:induction-lists}

如同第\@ref{sec:lists}節所述，「元素型別為|a|的串列」可定義成如下的資料型別：^[Haskell 中「元素型別為|a|的串列」寫成|[a]|. 由於這樣的符號在教學中遇到許多困難，本書中寫成|List a|.]
```spec
data List a = [] | a : List a {-"~~."-}
```
{.nobreak}這個定義可以理解為

  1. |[]| 是一個串列，
  2. 若 |xs| 是一個元素型別為|a|的串列，|x| 型別為 |a|, 則 |x:xs| 也是一個元素型別為|a|的串列，
  3. 此外沒有其他元素型別為|a|的串列。

我們不難發現 |List a| 和 |Nat| 是相當類似的資料結構：|[]| 相當於 |Zero|, |(:)| 則類似 |Suc|, 只是此處我們不只「加一」，添加的那個東西多了一些資訊，是一個型別為|a|的元素。
或著我們可反過來說，串列「只是」在每個|Suc|上都添了一些資訊的自然數！
既然自然數與串列有類似的結構，不難想像許多自然上的函數、自然數的性質，都有串列上的類似版本，

### 串列上之歸納定義 {#sec:induction-lists-defn}

和自然數類似，許多串列上的函數可歸納地定義出來。
由於串列只可能由|[]|或|(:)|做出，定義串列上的函數時也分別處理這兩個情況。
基底情況為|[]|, 而欲定義 |f (x:xs)| 的值時，可假設 |f xs| 已算出來了：
```spec
f :: List a -> b
f []      = e
f (x:xs)  = ... f xs ...
```
{.nobreak}來看些例子吧！「算一個陣列的和」可能是許多人學到陣列後得寫的頭幾個練習程式。串列版的和可以這麼寫：
```spec
sum :: List Int -> Int
sum []      = 0
sum (x:xs)  = x + sum xs {-"~~."-}
```
{.nobreak}基底狀況中，空串列的和應是|0|。歸納步驟中，我們要算|x:xs| 的和，可假設我們已算出|xs| 的和，再加上|x| 即可。計算串列長度的 |length| 有很類似的定義 ：
```haskell
length :: List a -> Nat
length []      = Zero
length (x:xs)  = Suc (length xs) {-"~~."-}
```
{.nobreak}在歸納步驟中，我們想計算|x:xs| 的長度，只需假設我們已知|xs| 的長度，然後加一。
事實上，|length| 剛好體現了前述「|List a| 只是在每個|Suc|上添了資訊的自然數」一事：
|length| 把串列走過一遍，將 |[]| 代換成 |Zero|，並將每個 |(_:)| 中附加的資訊拋棄，代換成 |Suc|。

函數 |map f :: List a -> List b|，也就是 |map| 給定函數 |f| 的結果，也可在串列上歸納定義：
```spec
map :: (a -> b) -> List a -> List b
map f []      = []
map f (x:xs)  = f x : map f xs {-"~~."-}
```
{.nobreak}基底狀況的合理結果是|[]|. 歸納步驟中，要對 |x:xs| 中的每個元素都做 |f|,
我們可假設已經知道如何對 |xs| 中的每個元素都做 |f|, 把其結果接上 |f x| 即可。

函數 |(++)| 把兩個串列接起來。如果我們在其左邊的參數上做歸納定義，可得到：
^[依照 Haskell 的運算元優先順序，|x : (xs ++ ys)| 其實可寫成 |x : xs ++ ys|, 一般也常如此寫。此處為了清楚而加上括號。]
```spec
(++) :: List a -> List a -> List a
[]      ++ ys  = ys
(x:xs)  ++ ys  = x : (xs ++ ys) {-"~~."-}
```
{.nobreak}空串列接上 |ys| 仍是 |ys|. 歸納步驟中，要把 |x:xs| 接上 |ys|, 我們可假設已有辦法把 |xs| 接上 |ys|, 然後只需添上 |x| 即可。

請讀者比較一下|(++)|與自然數加法|(+)|的定義，會發現兩者的結構一模一樣！
如果串列是在每個|Suc|中加上資料的自然數，|(++)|就是串列上的加法了。
若要形式化地把 |List a|, |Nat|, |(++)|, 與 |(+)| 牽上關係，連接他們的橋樑就是 |length| --- |xs ++ ys| 的長度，應是 |xs| 與 |ys| 的長度之和！意即：
```{.equation #eq:length-append}
  |length (xs ++ ys) = length xs + length ys| \mbox{~~.}
```
{.nobreak}習題 \@ref{ex:length-append} 中將證明此性質。

最後，|(++)| 是反覆使用 |(:)|, 函數 |concat| 則是反覆使用 |(++)|:
```spec
concat :: List (List a) -> List a
concat [] = []
concat (xs:xss) = xs ++ concat xss {-"~~."-}
```

### 串列上之歸納證明 {#sec:induction-lists-proof}

如果 |List a| 是一個歸納定義出的資料結構，我們應可以在 |List a| 之上做歸納證明。確實，串列上的歸納法可寫成：
```{.equation title="串列上之歸納法："}
  |(forall xs . P xs) {-"~"-}<== {-"~"-} P [] && (forall x xs . P (x:xs) <== P xs) {-"~~."-}|
```
{.nobreak}以文字敘述的話：給定一個述語 |P :: List a -> Bool|, 若要證明 |P xs| 對所有 |xs| 都成立，只需證明 |P []| 和「對所有 |x| 和 |xs|, 若 |P xs| 則 |P (x:xs)|」。

下述的 *|map| 融合定理*(*map-fusion theorem*)
\index{map-fusion map 融合定理@@{|map|-fusion |map| 融合定理}}
是關於 |map| 極常用的定理之一。所謂「融合」在此處是把兩個 |map| 融合為一。
我們日後會見到更多的融合定理。
::: {.theorem #thm:map-fusion title="|map| 融合定理"}
對任何 |f| 與 |g|,
|map f . map g = map (f.g)|.
:::
{.nobreak}作為一個例子，我們試著證明定理\@ref{thm:map-fusion}。
我們目前只會用歸納證明，但是 |map f . map g = map (f.g)| 的左右邊都是函數，
沒有出現串列也沒有出現自然數。該拿什麼東西來歸納呢？

回顧*外延相等*（定義\@ref{def:extensional-eq}）：
當|h|, |k| 均是函數，|h = k| 的意思是對任何參數 |x|, |h x = k x|.
因此，將待證式左右邊各補上參數，並將 |(.)| 展開，可得知其意義為對任何 |xs|,
```equation
    |map f (map g xs) = map (f.g) xs| \mbox{~ ~.}
```
{.nobreak}我們便可以在|xs|上做歸納了！
:::{.proof}
當 |xs := []|，等式兩邊皆歸約為 |[]|.
考慮 |xs := x:xs| 的情況：
```spec
  map f (map g (x:xs))
=   {- |map| 之定義 -}
  map f (g x : map g xs)
=   {- |map| 之定義 -}
  f (g x) : map f (map g xs)
=   {- |(.)| 之定義 -}
  (f.g) x : map f (map g xs)
=   {- 歸納假設 -}
  (f.g) x : map (f.g) xs
=   {- |map| 之定義 -}
  map (f.g) (x:xs) {-"~~."-}
```
:::

:::{.texonly}
% 前面說到 |(++)| 與 |(+)| 的相似性。若要形式化地把 |List a|, |Nat|, |(++)|, 與 |(+)|
% 牽上關係，連接他們的橋樑就是 |length| --- |xs ++ ys| 的長度，應是 |xs| 與 |ys| 的長度之和！我們試著證明看看。
% \begin{theorem} \label{thm:length-append}
% 對所有 |xs| 與 |ys|, |length (xs ++ ys) = length xs + length ys|.
% \end{theorem}
% \begin{proof} 檢視 |length|, |(++)|, 與 |(+)| 的定義，會發現等號兩邊都須對 |xs| 做分析才能化簡。因此我們對 |xs| 做歸納。
%
% \noindent {\bf 狀況} |xs := []|.
% %if False
% ```haskell
% lengthAppendPf0 ys =
% ```
% %endif
% ```haskell
%       length ([] ++ ys)
%  ===    {- |(++)| 之定義 -}
%       length ys
%  ===   {- |(+)| 之定義 -}
%       Zero +: length ys
%  ===   {- |length| 之定義 -}
%       length [] +: length ys {-"~~."-}
% ```
%
% \noindent {\bf 狀況} |xs := x : xs|.
% %if False
% ```haskell
% lengthAppendPf1 :: a -> List a -> List a -> Nat
% lengthAppendPf1 x xs ys =
% ```
% %endif
% ```haskell
%    length ((x:xs) ++ ys)
%  ===    {- |(++)| 之定義  -}
%    length (x : (xs ++ ys))
%  ===    {- |length| 之定義 -}
%    Suc (length (xs ++ ys))
%  ===    {- 歸納假設 -}
%    Suc (length xs +: length ys)
%  ===    {- |(+)| 之定義 -}
%    (Suc (length xs)) +: length ys
%  ===    {- |length| 之定義 -}
%    length (x:xs) +: length ys {-"~~."-}
% ```
% \end{proof}
% 讀者可觀察到類似的技巧：在|xs := x : xs|的狀況中，頭幾步的目的是將|length|往裡推，製造出|length (xs++ys)|, 以便使用歸納假設。
:::

:::{.infobox title="等式證明的步驟該多詳細？"}
本書中目前為止的等式證明相當細：每一個定義展開都成為獨立的步驟。
這是為了教學目的，實務上不一定得如此。
以我而言，自己的研究手稿中可能會將步驟寫得極詳細，
為確保每個細節正確，並讓他人（或幾年後已經忘記細節的自己）在不需知道上下文的情況下也能機械化地檢查每個步驟。
但在論文中，因篇幅有限，及考量讀者一次能處理的資訊量有限，
發表出的證明可能會省略許多步驟。

實務上，被認為簡單、不寫出也不妨礙理解的步驟或說明都可被省略。
但何謂簡單則很依靠作者的判斷與習慣。
一般說來，僅展開定義的步驟用電腦便可自動做到，通常是可精簡掉的。
最好寫出的步驟則可能是決定整個證明之結構的、不易以電腦決定而得靠人類智慧與經驗的，等等。
這可能包括使用歸納假設的那步，或使用較特別的引理時。
例如，性質 \@ref{eq:length-append}的歸納步驟證明可能被精簡如下：
```spec
   length ((x:xs) ++ ys)
=  Suc (length (xs ++ ys))
=    {- 歸納假設 -}
   Suc (length xs +: length ys)
=  length (x:xs) +: length ys {-"~~."-}
```
:::

:::{.exlist}
:::{.exer #ex:append-nil}
證明對所有 |xs|, |xs ++ [] = xs|. 比較本題與習題\@ref{ex:add-right-id}的證明。
:::
:::{.exer #ex:reverse}
定義函數 |reverse :: List a -> List a|, 將輸入的串列反轉。例如 |reverse [1,2,3,4,5] = [5,4,3,2,1]|.
:::
:::{.exans .compact}
```spec
reverse :: List a -> List a
reverse []      = []
reverse (x:xs)  = reverse xs ++ [x] {-"~~."-}
```
{.nobreak}另，關於 |reverse| 效率的討論詳見第 \@ref{sec:efficiency-basics} 節。
:::
:::{.exer #ex:length-map}
證明對所有 |f|, |length . map f = length|.
:::
:::{.exer #ex:sum-map-times}
證明對所有 |x|, |sum . map (x*) = (x*) . sum|.
:::
:::{.exans}
欲證明|sum (map (x*) ys) = x * sum ys|, 在 |ys| 上歸納。

{.noindent}**情況** |ys := []|, 兩邊都歸約為 |0|.

{.noindent}**情況** |ys := y:ys|:
```spec
   sum (map (x*) (y:ys))
=    {- |map| 之定義 -}
   sum (x*y : map (x*) ys)
=    {- |sum| 之定義 -}
   x * y + sum (map (x*) ys)
=    {- 歸納假設 -}
   x * y + x * sum ys
=    {- 乘法與加法之分配律 -}
   x * (y+sum ys)
=    {- |sum| 之定義 -}
   x * sum (y:ys) {-"~~."-}
```
:::
:::{.exer #ex:sum-map-suc}
證明對所有 |xs|, |sum (map (Suc) xs) = length xs + sum xs|.
:::
:::{.exer #ex:sum-map-const}
證明對所有 |xs| 與 |y|,
|sum (map (const y) xs) = y * length xs|.
:::
:::

討論自然數時，習題\@ref{ex:add-associative}曾請讀者證明加法都滿足結合律。此處示範證明類似定理的串列版：
::: {.theorem #thm:append-associative}
|(++)| 滿足結合律。意即，對任何 |xs|, |ys|, 和|zs|,
|(xs ++ ys) ++ zs = xs ++ (ys ++ zs)|.
:::
::: {.proof}
上述式子中有三個變數，我們怎麼得知該在哪一個變數上做歸納呢？
此時絕對別急著把三個變數都拆開，變成多達八種狀況。
觀察：如果要歸約等號左邊的 |(xs ++ ys) ++ zs|，根據 |(++)| 的定義，得對 |xs ++ ys| 做狀況分析；要歸約 |xs ++ ys|，又得對 |xs| 做狀況分析。
同樣地，根據 |(++)| 的定義，要歸約等號右邊的 |xs ++ (ys ++ zs)| 得對 |xs| 做狀況分析。
不論左右邊，最關鍵的值都是 |xs|.
因此我們在 |xs| 之上做歸納。

{.nobreak}**狀況** |xs:=[]|:
```spec
   ([] ++ ys) ++ zs
=   {- |(++)| 之定義 -}
   ys ++ zs
=   {- |(++)| 之定義 -}
   [] ++ (ys ++ zs) {-"~~."-}
```

{.nobreak}**狀況** |xs:= x:xs|:
```spec
   ((x:xs) ++ yz) ++ zs
=    {- |(++)| 之定義 -}
   (x : (xs ++ ys)) ++ zs
=    {- |(++)| 之定義 -}
   x : ((xs ++ ys) ++ zs)
=    {- 歸納假設 -}
   x : (xs ++ (ys ++ zs))
=    {- |(++)| 之定義 -}
   (x : xs) ++ (ys ++ zs) {-"~~."-}
```
:::
基底狀況的證明很簡單。至於歸納步驟，同樣地，前兩步都是為了湊出 |(xs ++ ys) ++ zs|, 以便使用歸納假設。既然 |(++)| 滿足結合律，日後我們寫 |xs ++ ys ++ zs| 就可不加括號了。

:::{.exlist}
:::{.exer #ex:length-append}
證明性質\@eqref{eq:length-append}：對所有 |xs| 與 |ys|, |length (xs ++ ys) = length xs + length ys|.
:::
:::{.exans}
檢視 |length|, |(++)|, 與 |(+)| 的定義，會發現等號兩邊都須對 |xs| 做分析才能化簡。因此我們對 |xs| 做歸納。

{.nobreak}**狀況** |xs := []|.
```{.haskell .invisible}
lengthAppendPf0 ys =
```
```haskell
      length ([] ++ ys)
 ===    {- |(++)| 之定義 -}
      length ys
 ===   {- |(+)| 之定義 -}
      Zero +: length ys
 ===   {- |length| 之定義 -}
      length [] +: length ys {-"~~."-}
```

{.nobreak}**狀況**  |xs := x : xs|.
```{.haskell .invisible}
lengthAppendPf1 :: a -> List a -> List a -> Nat
lengthAppendPf1 x xs ys =
```
```haskell
   length ((x:xs) ++ ys)
 ===    {- |(++)| 之定義  -}
   length (x : (xs ++ ys))
 ===    {- |length| 之定義 -}
   Suc (length (xs ++ ys))
 ===    {- 歸納假設 -}
   Suc (length xs +: length ys)
 ===    {- |(+)| 之定義 -}
   (Suc (length xs)) +: length ys
 ===    {- |length| 之定義 -}
   length (x:xs) +: length ys {-"~~."-}
```
:::
:::{.exer #ex:map-append}
證明對所有 |f|, |xs|, 與 |ys|, |map f (xs ++ ys) = map f xs ++ map f ys|.
:::
```texonly
%\Exercise 完成定理\@ref{thm:map-fusion}的證明。
% \Answer 欲證明|map f (map g xs) = map (f.g) xs|, 在 |xs| 上歸納。
%
% \noindent{\bf 情況} |xs := []|, 兩邊都歸約為 |[]|.
%
% \noindent{\bf 情況} |xs := x:xs|:
% ```spec
%   map f (map g (x:xs))
% =   {- |map| 之定義 -}
%   map f (g x : map g xs)
% =   {- |map| 之定義 -}
%   f (g x) : map f (map g xs)
% =   {- |(.)| 之定義 -}
%   (f.g) x : map f (map g xs)
% =   {- 歸納假設 -}
%   (f.g) x : map (f.g) xs
% =   {- |map| 之定義 -}
%   map (f.g) (x:xs) {-"~~."-}
% ```
```
:::


## 從資料、程式、到證明 {#sec:data-prog-proof}

本節再用一個例子談談「讓符號為我們工作」。考慮證明下述性質：
```{.equation #eq:sum-concat}
 |sum . concat = sum . map sum|\mbox{~ ~.}
```
根據外延相等，這相當於證明對所有|xss|,
|sum (concat xss) = sum (map sum xss)|.
當 |xss := []|, 等號兩邊都歸約成 |0|. 考慮 |xss := xs :xss| 的情況：
```{.haskell .invisible}
sumConcatInd :: List Int -> List (List Int) -> Int
sumConcatInd xs xss =
```
```haskell
      sum (concat (xs:xss))
 ===    {- |concat| 之定義 -}
      sum (xs ++ concat xss)
 ===    {- 因 |sum (xs ++ ys) = sum xs + sum ys| -}
      sum xs + sum (concat xss)
 ===    {- 歸納假設 -}
      sum xs + sum (map sum xss)
 ===    {- |sum| 之定義 -}
      sum (sum xs : map sum xss)
 ===    {- |map| 之定義 -}
      sum (map sum (xs:xss)) {-"~~."-}
```
{.nobreak}讀者對這個證明最大的疑問可能是：我們怎麼知道該用 |sum (xs ++ ys) = sum xs + sum ys| 呢？
為什麼當我們遇到 |sum (xs ++ concat xss)|, 我們不是把 |xs| 再拆成首和尾，甚至把 |xss| 拆開？
這是許多綜合考量的結果。
首先，我們預期會使用歸納假設，因此證明前幾步的目的均為把 |sum| 推到 |concat xss| 左側，試圖做出 |sum (concat xss)|.
此處我們再強調一個觀念：*證明中的步驟不是瞎猜的，而是有目的的*。
符號給我們提示：我們需要把 |sum| 往右推，因此我們試圖尋找能完成這個目標的性質。

其次，*證明的結構跟隨著程式的結構*。由於 |concat| 是由 |(++)| 定義的，每一個關於 |concat| 的定理，均很有可能奠基在一個關於 |(++)| 的相對定理上。為了證明一個描述 |sum| 與 |concat| 的關係的定理，我們可能會需要一個關於 |sum| 與 |(++)| 的性質。

有了符號給我們的這兩個線索，我們便可以運用我們對語意的了解：|sum| 與 |(++)| 應該會滿足什麼性質？
我們可猜測應該是 |sum (xs ++ ys) = sum xs + sum ys| --- 根據我們對 |sum| 與 |(++)| 的語意上的理解，這性質成立的機會很大。
而且，這個性質允許我們把 |sum| 推到右邊。

符號仍舊幫助了我們。
我們不可能期待所有定理都只靠符號推導出，在關鍵時刻我們仍會需要對於特定領域的、語意上的知識。但符號給了我們許多引導，
縮小我們需要猜測的範圍。

至於 |sum (xs ++ ys) = sum xs + sum ys| 該怎麼證明呢？
不要急著把 |xs| 與 |ys| 都拆開。
觀察等號左右邊的式子，根據 |(++)|, |(+)| 與 |sum| 的定義，兩個式子的歸約都是先對 |xs| 做情況分析。
因此我們可試著在 |xs| 上做歸納。

*證明的結構跟隨著程式的結構* --- 這是做證明時相當好用的指引。
程式對哪個參數做歸納，我們做證明時就在那個參數上做歸納。
函數 |f| 用函數 |g| 定義，我們證明 |f| 的性質時就可以預期會需要一個 |g| 的相關性質。
並非所有證明都可以如此做出，但這個模式在許多情況下都適用。

而如我們所知，*程式的結構又跟隨著資料的結構*：
例如，串列有 |[]| 和 |x:xs| 兩個情況，我們定義串列上的程式時也分出這兩個情況，
定義 |f (x:xs)| 時可以使用 |f xs| 的值。
資料結構、程式、與證明於是有著這樣的連續關係：
歸納定義出一個資料結構，我們就有了一個在上面歸納定義程式的方法；
有了歸納定義的程式，我們便知道怎麼做關於它的歸納證明。
一切由資料結構開始。

:::{.exlist}
:::{.exer #ex:length-concat}
證明 |length . concat = sum . map length|.
我們會需要什麼關於 |(++)| 的相關性質？
:::
:::{.exans}
考慮 |xs:xss| 的情況：
```spec
     length (concat (xs:xss))
===  length (xs ++ concat xss)
===    {- 因 |length (xs ++ ys) = length xs + length ys| -}
     length xs + length (concat xss)
===    {- 歸納假設 -}
     length xs + sum (map length xss)
===  sum (length xs : map length xss)
===  sum (map length (xs:xss)) {-"~~."-}
```
{.nobreak}我們需要的性質是 |length (xs ++ ys) = length xs + length ys| .
:::
:::{.exer #ex:map-concat}
證明對所有 |f|, |map f . concat = concat . map (map f)|.
我們會需要什麼關於 |(++)| 的相關性質？
:::
:::{.exans}
考慮 |xs:xss| 的情況：
```spec
     map f (concat (xs:xss))
===  map f (xs ++ concat xss)
===   {- 因 |map f (xs ++ ys) = map f xs ++ map f ys| -}
     map f xs ++ map f (concat xss)
===   {- 歸納假設 -}
     map f xs ++ concat (map (map f xss))
===  concat (map f xs : map (map f xss))
===  concat (map (map f (xs : xss))) {-"~~."-}
```
{.nobreak}我們需要的性質是 |map f (xs ++ ys) = map f xs ++ map f ys| .
:::
:::

## 更多歸納定義與證明 {#sec:more-inductive-defns}

為讓讀者熟悉，本節中我們多看一些自然數或串列上的歸納定義。

### |filter|, |takeWhile|, 與 |dropWhile| {#sec:filter-takeWhile-dropWhile}

{title="filter"} 我們曾見過的函數 |filter| 可寫成如下的歸納定義：
```spec
filter :: (a -> Bool) -> List a -> List a
filter p []      = []
filter p (x:xs)  = if p x then x : filter p xs else filter p xs {-"~~."-}
```
{.nobreak}在 |filter| 的許多性質中，我們試著證明下述性質作為例子：
:::{.theorem #thm:filter-map}
|filter p . map f = map f . filter (p . f)|.
:::
:::{.proof}
和定理\@ref{thm:map-fusion}一樣，待證式的左右邊都是函數。
根據外延相等，我們將左右邊各補上參數 |xs|，並在 |xs| 上做歸納：
```equation
  |filter p (map f xs) = map f (filter (p . f) xs)| \mbox{~~.}
```
情況 |x := []| 中左右邊都可化簡成|[]|.
我們看看 |xs := x:xs| 的情況：
```{.haskell .invisible}
filterMapPf1 p f x xs =
```
```haskell
   filter p (map f (x:xs))
 ===    {- |map| 之定義 -}
   filter p (f x : map f xs)
 ===    {- |filter| 之定義 -}
   if p (f x)  then f x : filter p (map f xs) else filter p (map f xs)
 ===    {- 歸納假設 -}
   if p (f x)  then f x : map f (filter (p . f) xs) else map f (filter (p . f) xs)
 ===    {- |map| 之定義 -}
   if p (f x)  then map f (x : filter (p . f) xs) else map f (filter (p . f) xs)
 ===    {- 因 |f (if p then e1 else e2) = if p then f e1 else f e2|, 如後述 -}
   map f (if p (f x) then x : filter (p . f) xs else filter (p . f) xs)
 ===    {- |filter| 之定義 -}
   map f (filter (p . f) (x:xs)) {-"~~."-}
```
:::

{title="終止與證明"}
上述證明的倒數第二步為將 |map f| 提到外面，用了一個關於 |if| 的性質：
```{.equation #eq:fn-if-distribute}
  |f (if p then e1 else e2) {-"~"-}={-"~"-} if p then f e1 else f e2| \mbox{~~.}
```
這性質對嗎？若 |p| 成立，左右手邊都化簡為|f e1|, 若 |p| 不成立，左右手邊都化簡為 |f e2|. 因此 \@eqref{eq:fn-if-distribute} 應該成立，是嗎？

答案是：如果我們假設的世界中有不終止的程式，\@eqref{eq:fn-if-distribute}便不正確了。
例如，當 |f| 是 |three x = 3|，而 |p| 是個永遠執行、不終止的算式（例：|let b = not b in b|)：
```{.equation #eq:fn-if-three-distribute}
  |three (if p then e1 else e2) {-"~\stackrel{?}{=}~"-} if p then three e1 else three e2| {-"~~."-}
```
{.nobreak}上述式子的左手邊直接化簡成|3|, 但右手邊卻不會終止，因為 |if| 得知道 |p| 的值。
我們找到了 \@eqref{eq:fn-if-distribute} 的反例！

在允許可能不終止的程式存在的世界中，\@eqref{eq:fn-if-distribute}得多些附加條件。
通常的做法是限定 |f| 須是個*嚴格函數*, 意即 |f| 的輸入若不終止，|f|也不會終止。
但\@eqref{eq:fn-if-distribute}並不是唯一帶著附加條件的性質 --- 許多常用性質都得加上類似的附加條件。
所有狀況分析也都得將不終止考慮進去，例如，自然數除了 |Zero| 與 |Suc n| 之外，還多了第三種情況「不終止」。^[@Bird:87:Introduction 就採用這種作法。]
推論與證明變得更複雜。
有些人因此較喜歡另一條路：藉由種種方法確保我們只寫出會終止的程式，便可假設我們確實活在所有程式都正常終止的世界中。

{title="保護式 v.s. 條件分支"} 有些人喜歡用保護式語法定義 |filter|：
```spec
filter p []      = []
filter p (x:xs)  | p x        = x : filter p xs
                 | otherwise  = filter p xs {-"~~."-}
```
{.nobreak}若在此定義下證明定理\@ref{thm:filter-map}，依「證明的結構與程式的結構相同」的原則，順理成章地，我們可在 |xs:=x:xs| 中再分出 |p (f x)| 成立與不成立的兩個子狀況：
```spec
 {-"\mbox{\bf 狀況}~"-} xs:=[]:  ...
 {-"\mbox{\bf 狀況}~"-} xs:=x:xs: ...
    {-"\mbox{\bf 狀況}~"-} p (f x):
         filter p (map f (x:xs))
      =    {- |p (f x)| 成立 -}
         f x : filter p (map f xs)
      =  ... {-"~~."-}
    {-"\mbox{\bf 狀況}~"-} not (p (f x)):
         filter p (map f (x:xs))
      =   {- |(not p (f x))| -}
         filter p (map f xs)
      =  ... {-"~~."-}
```
{.nobreak}這個定義中不用 |if|, 因此證明中也用不上 \@eqref{eq:fn-if-distribute}, 但該證明要成立仍須假設所有程式都正常終止 --- 我們少證了一個 「|p (f x)| 不終止」的情況（而確實，在此情況下\@eqref{eq:fn-if-distribute}並不成立）。喜歡用哪個方式純屬個人偏好。

前幾章提過的 |takeWhile| 與 |dropWhile| 兩函數型別與 |filter| 相同。他們可寫成如下的歸納定義：
```spec
takeWhile :: (a -> Bool) -> List a -> List a
takeWhile p []      = []
takeWhile p (x:xs)  = if p x then x : takeWhile p xs else [] {-"~~,"-}

dropWhile :: (a -> Bool) -> List a -> List a
dropWhile p []      = []
dropWhile p (x:xs)  = if p x then dropWhile p xs else x:xs {-"~~."-}
```
{.nobreak}兩者都是在輸入串列上做歸納。兩者也都可用保護式語法定義。

:::{.exlist}
:::{.exer #ex:take-cat-drop}
證明 |takeWhile p xs ++ dropWhile p xs = xs|.
:::
:::{.exer #ex:protect-takeWhile-dropWhile}
以保護式語法定義 |takeWhile| 與 |dropWhile|, 以此定義做做看習題 \@ref{ex:take-cat-drop}.
:::
:::



### |elem| 與不等式證明 {#sec:elem-neq-proof}

{title="不等式證明"} 給定如下的定義，|elem x xs| 判斷 |x| 是否出現在串列 |xs| 中：
```spec
elem x []      = False
elem x (y:xs)  = (x == y) || elem x xs {-"~~."-}
```
% 在 Haskell 中 |elem| 的型別是 |Eq a => a -> List a -> Bool|.
% 我們將在第???章詳細解釋 |Eq a =>| 的部分。
% 目前可粗略地理解為：|elem| 檢查某型別為 |a| 的元素是否出現在型別為 |List a| 的串列中，但有個附加條件：屬於型別 |a| 的值必須能判斷是否相等。
目前為止，我們所練習的都是以|(=)|將式子串起的等式證明。
以下以|elem|為例，我們嘗試證明一個「不等式」：
```spec
  elem z xs {-"~"-}==>{-"~"-} elem z (xs ++ ys) {-"~~."-}
```
{.nobreak}以口語說出的話：「若|z| 出現在|xs| 中，|z| 也出現在|xs ++ ys| 中」。
欲證明上式，該從哪一側推到哪一側呢？
一般認為從式子較長、或結構較複雜的那側開始，化簡成較短、較簡單的那側，是較容易的。
因此我們嘗試由右側推到左側：由 |elem z (xs ++ ys)| 開始，尋找使之成立的條件，
並希望 |elem z xs| 是足夠的。
:::{.proof}
在 |xs| 上做歸納。基底 |xs := []| 的狀況在此省略，
看 |xs:=x:xs| 的狀況：
```spec
     elem z ((x:xs) ++ ys)
<=>   {- |(++)| 之定義 -}
     elem z (x : (xs ++ ys))
<=>   {- |elem| 之定義 -}
     (z==x) || elem z (xs ++ ys)
<==   {- 歸納假設 -}
     (z==x) || elem z xs
<=>   {- |elem| 之定義 -}
     elem z (x:xs) {-"~~."-}
```
:::
{.nobreak}讀者可注意：第1, 2, 4 步使用的邏輯關係都是 |(<=>)| ，第 3 步卻是 |(<==)|，因此整個證明建立了「若|elem z (x:xs)|，則|elem z ((x:xs) ++ ys)|」。

:::{.exlist}
:::{.exer #ex:weaken-not-elem}
證明 |not (elem z (xs ++ ys)) ==> not (elem z xs)|.
:::
:::{.exer #ex:elem-catleft}
證明 |elem z xs ==> elem z (ys ++ xs)|.
:::
:::{.exer #ex:all-monotonic}
證明|(forall x . p x ==> q x) ==> all p xs ==> all q xs|.
其中 |all| 的定義為：
```spec
all :: (a -> Bool) -> List a -> Bool
all p []      = True
all p (x:xs)  = p x && all p xs {-"~~."-}
```
:::
:::{.exer #ex:all-elem}
證明 |all (`elem` xs) (filter p xs)|. 其中 |x `elem` xs| 是 |elem x xs| 的中序寫法。 我們可能需要習題 \@ref{ex:elem-catleft} 和 \@ref{ex:all-monotonic} 的結果，以及下述性質：
```{.equation #eq:ifpxx}
    |if p then x else x| = |x| \mbox{~~.}
```
:::
:::{.exans}
在 xs 上做歸納。
```{.haskell .invisible}
allElemFilterPf1 p x xs =
```
```haskell
      all (`elem` (x:xs)) (filter p (x:xs))
 <=>  all (`elem` (x:xs)) (if p x then x:filter p xs else filter p xs)
 <=>  if p x  then all (`elem` (x:xs)) (x:filter p xs)
              else all (`elem` (x:xs)) (filter p xs)
 <=>  if p x  then x `elem` (x:xs) && all (`elem` (x:xs)) (filter p xs)
              else all (`elem` (x:xs)) (filter p xs)
 <==  if p x  then all (`elem` (x:xs)) (filter p xs)
              else all (`elem` (x:xs)) (filter p xs)
 <=>     {- \eqref{eq:ifpxx} -}
      all (`elem` (x:xs)) (filter p xs)
 <==     {- 因習題 \ref{ex:elem-catleft}, |z `elem` (x:xs) <== z `elem` xs| -}
      all (`elem` xs) (filter p xs)
 <==  True {-"~~."-}
```
:::
:::

### 串列區段 {#sec:list-segments}

{title="前段與後段"}
本章目前為止討論的歸納定義都依循著這樣的模式：欲定義 |f :: List a -> b|, 只要為 |f []| 與 |f (x:xs)| 找到定義。在定義後者時，只需定義出由 |f xs| 做出 |f (x:xs)| 的關鍵一步。
目前為止，這關鍵一步都是加一、加上一個元素等簡單的動作。現在我們來看些更複雜的例子。

例\@ref{ex:inits}中曾提及：如果一個串列 |xs| 可分解為 |ys ++ zs|, 我們說 |ys| 是 |xs| 的一個*前段(prefix)*,\index{list 串列!prefix 前段}
|zs| 是 |xs| 的一個*後段(suffix)*.\index{list 串列!suffix 後段}
例如，串列 |[1,2,3]| 的前段包括 |[]|, |[1]|, |[1,2]|, 與|[1,2,3]| （注意：|[]|是一個前段，串列 |[1,2,3]| 本身也是）, 後段則包括 |[1,2,3]|, |[2,3]|, |[3]|, 與 |[]|。我們是否能定義一個函數 |inits :: List a -> List (List a)|, 計算給定串列的所有前段呢？
例\@ref{ex:inits}給的答案是：
```spec
inits xs = map (\n -> take n xs) [0 .. length xs] {-"~~."-}
```
{.nobreak}如果不用組件，改用歸納定義呢？我們試試看：
```spec
inits :: List a -> List (List a)
inits []      = ?
inits (x:xs)  = ?
```
{.nobreak}基底狀況 |inits []| 的可能選擇是 |[[]]| （見後述）。至於歸納步驟該怎麼寫？
我們用例子來思考。比較 |inits [2,3]| 與 |inits [1,2,3]|:
```spec
  inits [2,3]    = [[],[2],[2,3]] {-"~~,"-}
  inits [1,2,3]  = [[],[1],[1,2],[1,2,3]] {-"~~."-}
```
{.nobreak}假設我們已算出 |inits [2,3]|, 如何把它加工變成 |inits [1,2,3]|? 請讀者暫停一下，思考看看！

一個思路是：如果在 |[[],[2],[2,3]]| 中的每個串列前面都補一個 |1|, 我們就有了 |[[1],[1,2],[1,2,3]]|. 再和 |inits [1,2,3]| 比較，就只差一個空串列了！
因此 |inits| 的一種定義方式是：
```haskell
inits :: List a -> List (List a)
inits []      = [[]]
inits (x:xs)  = [] : map (x:) (inits xs) {-"~~."-}
```

在此得提醒：有些讀者認為基底狀況 |inits []| 的值選為 |[[]]|，是因為結果的型別是 |List (List a)|
（直覺地把每個 |List| 都對應到一組中括號，或認為 |[[]]| 是型別為 |List (List a)| 的最簡單的值）。
但事實並非如此：畢竟，|[]| 的型別也可以是 |List (List a)|！
我們讓 |inits [] = [[]]| 的原因是空串列 |[]| 的「所有前段」只有一個，恰巧也是 |[]|。
就如同在自然數上的歸納函數定義中，有些基底狀況是 |0|, 有些是 |1|, 有些是別的值，
此處我們也依我們的意圖，選定最合適的基底值。

```texonly
%format initsp = "\Varid{inits}^{+}"
```
:::{.exlist}
:::{.exer #ex:initsp}
試定義 |initsp :: List a -> List (List a)|, 計算一個串列的所有*非空前段*。例如 |initsp [1,2,3]| 是 |[[1],[1,2],[1,2,3]]|。當然，其中一個定義方式是 |initsp = tail . inits|. 你能以歸納方式定義出 |initsp| 嗎？
```spec
initsp []      = ?
initsp (x:xs)  = ?
```
:::
:::{.exans .compact}
```haskell
initsp :: List a -> List (List a)
initsp []      = []
initsp (x:xs)  = [x] : map (x:) (initsp xs) {-"~~."-}
```
:::
:::{.exer #ex:inits-upto}
我們驗證一下 |inits| 在例\@ref{ex:inits} 中的組件定義與本章的歸納定義是相等的。定義 |upto :: Nat -> List Nat|:
```haskell
upto Zero     = [Zero]
upto (Suc n)  = 0 : map (Suc) (upto n) {-"~~."-}
```
{.nobreak}使得 |upto n = [0.. n]|.
假設 |inits| 已如本節一般地歸納定義，證明對所有 |xs|,
|inits xs = map (\n -> take n xs) (upto (length xs))|.
您可能會需要 |map| 融合定理（定理\@ref{thm:map-fusion}），
:::
:::{.exans}
在 |xs| 上做歸納。

{.noindent}**情況** |xs := []|. 此時等號兩邊都是 |[[]]|.

{.noindent}**情況** |xs := x:xs|.
```{.haskell .invisible}
initsEquival x xs =
```
```haskell
    map (\n -> take n (x:xs)) (upto (length (x:xs)))
 ===    {- |length| 之定義 -}
    map (\n -> take n (x:xs)) (upto (Suc (length xs)))
 ===    {- |upto| 之定義 -}
    map (\n -> take n (x:xs)) (0 : map (Suc) (upto (length xs)))
 ===    {- |length| 之定義 -}
    map (\n -> take n (x:xs)) (0 : map (Suc) (upto (length xs)))
 ===    {- |map|之定義，|take 0 (x:xs) = []| -}
    [] : map (\n -> take n (x:xs)) (map (Suc) (upto (length xs)))
 ===    {- 定理\ref{thm:map-fusion}：|map f . map g = map (f.g)| -}
    [] : map (\n -> take (Suc n) (x:xs)) (upto (length xs))
 ===    {- |take| 之定義 -}
    [] : map (\n -> x : take n xs) (upto (length xs))
 ===    {- 定理\ref{thm:map-fusion}：|map f . map g = map (f.g)| -}
    [] : map (x:) (map (\n -> take n xs) (upto (length xs)))
 ===    {- 歸納假設 -}
    [] : map (x:) (inits xs)
 ===    {- |inits| 之定義 -}
    inits (x:xs) {-"~~."-}
```
:::
:::

定義傳回後段的函數 |tails| 時可依循類似的想法：
如何把 |tails [2,3] = [[2,3],[3],[]]|加工，得到 |tails [1,2,3] = [[1,2,3],[2,3],[3],[]]|?
這次較簡單：加上 |[1,2,3]| 即可。
的確，串列 |x:xs| 的後段包括 |x:xs| 自己，以及 |xs| 的後段：
```haskell
tails :: List a -> List (List a)
tails []      = [[]]
tails (x:xs)  = (x:xs) : tails xs {-"~~."-}
```
{.nobreak}在習題 \@ref{ex:zip-inits-tails} 中我們將證明一個將 |inits| 與 |tails| 牽上關係的定理：將 |inits| 傳回的前段與 |tails| 傳回的後段照其順序對應，每對接起來都是原來的串列。

{title="連續區段"}
給定一個串列，許多傳統最佳化問題的目標是計算符合某條件的*連續區段*（簡稱「區段」）。\index{list 串列!segment 區段}
例如，|[1,2,3]| 的區段包括|[]|,|[1]|,|[2]|,|[3]|,|[1,2]|,|[2,3]|, 以及
|[1,2,3]|本身。
我們可用 |inits| 與 |tails| 得到一個串列的所有區段。
```haskell
segments :: List a -> List (List a)
segments = concat . map inits . tails {-"~~."-}
```
{.nobreak}但 |segments| 無法寫成本章目前這種形式的歸納定義。我們將在以後的章節再討論到 |segments|.

:::{.exlist}
:::{.exer #ex:segments-pattern}
試著把 |segments| 寫成如下的歸納定義：
```spec
segments :: List a -> List (List a)
segments []      = ?
segments (x:xs)  = ... segments xs ... {-"~~,"-}
```
{.nobreak}在歸納步驟中希望由 |segments xs| 湊出 |segments (x:xs)|。
這是能在不對輸入串列（型別為|List a|）做任何限制之下做得到的嗎？
如果做不到，為什麼？
:::
:::{.exans}
考慮如何從 |segments [1,2,3]| 湊出 |segments [0,1,2,3]|.
前者應當有的結果可能是：
```spec
[[],[1],[1,2],[1,2,3],[2],[2,3],[3]] {-"~~."-}
```
{.nobreak}而 |segments [0,1,2,3]| 的結果可能是：
```spec
[[],[0],[0,1],[0,1,2],[0,1,2,3],[1],[1,2],[1,2,3],[2],[2,3],[3]] {-"~~."-}
```
{.nobreak}乍看之下，要多做的一步是：在空串列或所有|1|開頭的串列前面補上 |0|.
之所以只擴充|1|開頭的串列，因為只有這些是原本便靠在左邊，和 |0| 相鄰的
（也就是說它們是|[1,2,3]|的前段）。

然而，當輸入串列型別為 |List a|（而不是特定的 |List Int|, |List Char| 時），我們無法用比較的方式找出這些前段。函數 |segments| 傳回的資訊不夠多。如果要歸納定義，我們必須把「前段」們和其他的區段分開。
:::
:::

### 插入、排列、子串列、與劃分 {#sec:fan-perm}

{title="排列"}
函數 |fan x xs| 把 |x| 插入 |xs| 的每一個可能空隙。例如，|fan 1 [2,3,4]| 可得到
|[[1,2,3,4],[2,1,3,4],[2,3,1,4],[2,3,4,1]]|. 讀者不妨想想它該怎麼定義？一種可能方式如下：
```haskell
fan :: a -> List a -> List (List a)
fan x []      = [[x]]
fan x (y:xs)  = (x:y:xs) : map (y:) (fan x xs) {-"~~."-}
```
{.nobreak}有了 |fan|, 我們不難定義 |perms :: List a -> List (List a)|, 計算一個串列所有可能
的*排列*。例如，|perms [1,2,3] = [[1,2,3], [2,1,3], [2,3,1], [1,3,2], [3,1,2], [3,2,1]]|：
```haskell
perms :: List a -> List (List a)
perms []      = [[]]
perms (x:xs)  = concat (map (fan x) (perms xs)) {-"~~."-}
```
{.nobreak}讀者可思考為何我們需要 |concat|? 如果沒有，會出現什麼錯誤？

基於 |perm| 的這個定義，我們證明一個定理：*長度為 |n| 的串列有 |fact n| 種排列*。
這個證明將使用到許多輔助性質與引理，有些已經是我們之前證明過的習題，有些則可作為接下來的習題。
在本證明之中我們也練習將連續的函數應用 |f (g (h x))| 寫成函數合成
|f . g . h $ x| 以方便計算。
:::{.theorem #thm:length-perms}
對任何 |xs|, |length (perms xs) = fact (length xs)|.
:::
:::{.proof}
在 |xs| 上做歸納。

\noindent{\bf 基底狀況} |xs:=[]|:
```{.haskell .invisible}
lengthPermsPf0 =
```
```haskell
      length (perms [])
 ===  length [[]]
 ===  1
 ===  fact (length []) {-"~~."-}
```
\noindent **歸納步驟** |xs := x:xs|:
```{.haskell .invisible}
lengthPermsPf1 x xs =
```
```haskell
      length (perms (x:xs))
 ===    {- |perms|, |(.)|, 與 |($)| 之定義 -}
      length . concat . map (fan x) . perms $ xs
 ===    {- 因 |length . concat = sum . map length| (習題\ref{ex:length-concat}), |map| 融合 -}
      sum . map (length . fan x) . perms $ xs
 ===    {- 因 |length . fan x = (Suc) . length| (習題 \ref{ex:length-fan}) -}
      sum . map ((Suc) . length) . perms $ xs
 ===    {- 因 |map length (perms xs) =|
 |map (const (length xs)) (perms xs)| (習題\ref{ex:map-length-perms})  -}
      sum . map ((Suc) . const (length xs)) . perms $ xs
 ===    {- 因 |sum (map (Suc) xs) = length xs + sum xs| (習題\ref{ex:sum-map-suc})-}
      length (perms xs) +: sum (map (const (length xs)) (perms xs))
 ===    {- 因 |sum (map (const y) xs) = y * length xs| (習題\ref{ex:sum-map-const}) -}
      length (perms xs) +: length xs *: length (perms xs)
 ===    {- 四則運算: |x + y * x = (1+y) * x| -}
      (Suc (length xs)) *: length (perms xs)
 ===    {- 歸納假設 -}
      (Suc (length xs)) *: fact (length xs)
 ===    {- |fact| 之定義 -}
      fact (Suc (length xs))
 ===    {- |length| 之定義 -}
      fact (length (x:xs)) {-"~~."-}
```
:::

:::{.exlist}
:::{.exer #ex:map-fan}
證明 |map f . fan x = fan (f x) . map f|.
:::
:::{.exer #ex:perm-map}
證明 |perm . map f = map (map f) . perm|.
:::
:::{.exer #ex:length-fan}
證明 |length (fan x xs) = Suc (length xs)|.
:::
:::{.exans}
在 |xs| 上做歸納。基底狀況很容易成立。考慮 |xs := y:xs|:
```{.haskell .invisible}
lengthFan x y xs =
```
```haskell
      length (fan x (y:xs))
 ===  length ((x:y:xs) : map (y:) (fan x xs))
 ===  Suc (length (map (y:) (fan x xs)))
 ===   {- 因 |length . map f = length| (練習 \ref{ex:length-map}) -}
      Suc (length (fan x xs))
 ===   {- 歸納假設 -}
      Suc (Suc (length xs))
 ===  Suc (length (y:xs)) {-"~~."-}
```
:::
:::{.exer #ex:map-length-perms}
證明 |perms xs| 傳回的每個串列都和 |xs| 一樣長，也就是 |map length (perms xs) = map (const (length xs)) (perms xs)|.
其中 |const| 定義於第 \@pageref{para:const} 頁 --- |const y| 是一個永遠傳回 |y| 的函數。
:::
:::{.exans}
欲證明 |map length (perms xs) = map (const (length xs)) (perms xs)|, 在 |xs| 之上做歸納。基底狀況 |xs := []| 中，等號兩邊都化約為 |[0]|. 考慮歸納步驟 |xs := x:xs|:
```{.haskell .invisible}
repeatN :: a -> Nat -> List a
repeatN x n = take n (repeat x)

mapLengthPermsInd x xs =
```
```haskell
  map length (perms (x:xs))
 ===   {- |perms| 之定義 -}
  map length . concat . map (fan x) . perms $ xs
 ===   {- |map f . concat = concat . map (map f)| (習題\ref{ex:map-concat}), |map| 融合 -}
  concat . map (map length . fan x) . perms $ xs
 ===   {- |map length . fan x = (\n -> repeatN n n) . length| -}
  concat . map ((\n -> repeatN n n) . (Suc) . length) . perms $ xs
 ===   {- |map| 融合 -}
  concat . map ((\n -> repeatN n n) . (Suc)) . map length . perms $ xs
 ===   {- 歸納假設 -}
  concat . map ((\n -> repeatN n n) . (Suc)) . map (const (length xs)) . perms $ xs
 ===   {- |map| 融合 -}
  concat . map ((\n -> repeatN n n) . (Suc) . const (length xs)) . perms $ xs
 ===   {- 歸約 $\lambda$ 算式 -}
  concat . map (repeatN (Suc (length xs)) . (Suc) . length) . perms $ xs
 ===   {- |length . fan x = (Suc) . length| (習題\ref{ex:length-fan})-}
  concat . map (repeatN (Suc (length xs)) . length . fan x) . perms $ xs
 ===   {- \todo{???} |map (const y) = repeatN y . length| -}
  concat . map (map (const (Suc (length xs))) . fan x) . perms $ xs
 ===   {- |map f . concat = concat . map (map f)| (習題\ref{ex:map-concat}) -}
  map (const (length (x:xs))) . concat . map (fan x) . perms $ xs
 ===   {- |perms| 之定義 -}
  map (const (length (x:xs))) (perms (x:xs)) {-"~~."-}
```
:::
:::

{title="子串列"}
函數 |sublists :: List a -> List (List a)| 計算一個串列的所有*子串列*。
後者是類似子集合的概念，只是把順序也考慮進去： |ys| 是 |xs| 的子串列，
如果將 |xs| 中的零個或數個元素移除後可得到 |ys|:
例如 |sublists [1,2,3]| 的結果可能是： |[[],[3],[2],[2,3],[1],[1,3],[1,2],[1,2,3]]|。
怎麼定義 |sublists| 呢？在基底狀況中，空串列仍有一個子串列 |[]|.
歸納步驟中，|x:xs| 的子串列可分為兩種：不含 |x| 的，以及含 |x| 的。
不含 |x| 的子串列就是 |xs| 的所有子串列（以下稱作 |yss|），
而含 |x| 的子串列就是 |yss| 中的每個串列接上 |x|. 因此我們可定義：
```haskell
sublists :: List a -> List (List a)
sublists []      = [[]]
sublists (x:xs)  = yss ++ map (x:) yss {-"~~,"-}
    where yss = sublists xs {-"~~."-}
```

:::{.exlist}
:::{.exer #ex:splits}
定義 |splits :: List a -> List (List a :* List a)|，
使 |splits xs| 傳回所有滿足 |ys ++ zs| 的 |(ys,zs)|.
例：
```equation
   &|splits [1,2,3] = [([],[1,2,3]), ([1],[2,3]), ([1,2],[3]), ([1,2,3,[]])]|\mbox{~~.}
```
{.nobreak}另一種說法是 |splits xs = zip (inits xs) (tails xs)|.
:::
:::{.exans .compact}
```haskell
splits :: List a -> List (List a :* List a)
splits []      = [([],[])]
splits (x:xs)  = ([],x:xs) : map ((x:)***id) (splits xs) {-"~~."-}
```
{.nobreak}其中 |(f *** g) (x,y) = (f x, g y)|, 定義於第 \@ref{sec:pairs} 節。
:::
:::{.exer #ex:length-sublists}
證明 |length . sublists = exp 2 . length|. 也就是說，長度為 |n| 的串列的子串列數目為 $2^n$. 你會需要的性質可能包括 \@eqref{eq:length-append} (|length (xs++ys) = length xs + length ys|), 以及 |length . map f = length|.
:::
:::{.exans}
將式子改寫為 |length (sublists xs) = exp 2 (length xs)|, 在 |xs| 上做歸納。
歸納步驟 |xs := x:xs| 為：
```{.haskell .invisible}
lengthSublists x xs =
```
```haskell
      length (sublists (x:xs))
 ===  length (sublists xs ++ map (x:) (sublists xs))
 ===    {- 因 \eqref{eq:length-append} |length (xs++ys) = length xs + length ys|  -}
      length (sublists xs) +: length (map (x:) (sublists xs))
 ===    {- 因 |length . map = length| (練習 \ref{ex:length-map})-}
      length (sublists xs) +: length (sublists xs)
 ===    {- 因 |x + x = 2 * x| -}
      2 *: length (sublists xs)
 ===    {- 歸納步驟 -}
      2 *: exp 2 (length xs)
 ===  exp 2 (Suc (length xs))
 ===  exp 2 (length (x:xs)) {-"~~."-}
```
:::
:::

```texonly
% ```spec
%   elem z xs ==> elem z (ys ++ xs)
% ```
% ```spec
%     elem z ((y:ys) ++ xs)
% <=>
%     elem z (y : (ys ++ xs))
% <=>
%     (z==y) || elem z (ys ++ xs)
% <==
%     (z==y) || elem z xs
% ```

% exercise
%   not (elem z (xs ++ ys)) ==> not (elem z xs)
%
%      not (elem z ((x:xs) ++ ys))
% <=>
%      not (elem z (x : (xs ++ ys)))
% <=>
%      not ((z==x) || elem z (xs ++ ys))
% <=>
%      z /= x && not (elem z (xs ++ ys))
% ==>
%      z /= x && not (elem z xs)
% <=>  not (elem z (x:xs))

% ```spec
%   all (`elem` xs) (filter p xs)
% ```
%
% ```spec
%    all (`elem` (x:xs)) (filter p (x:xs))
% =  all (`elem` (x:xs))
%      (if p x then x: filter p xs else filter p xs)
% =  if p x  then all (`elem` (x:xs)) (x : filter p xs)
%            else all (`elem` (x:xs)) (filter p xs)
% =  if p x  then x `elem` (x:xs) && all (`elem` (x:xs)) (filter p xs)
%            else all (`elem` (x:xs)) (filter p xs)
% ```
```


{title="劃分"}
給定串列 |xs :: List a|. 如果 |yss :: List (List a)| 滿足
  1. |concat yss = xs|,
  2. |yss| 中的每個串列都不是空的，
我們便說 |yss| 是 |xs| 的一個*劃分*(*partition*)。
例如，|[[1],[2,3],[4]]| 是 |[1,2,3,4]| 的一個劃分。\index{partition 劃分}

我們是否能定義一個函數 |parts :: List a -> List (List (List a))|,
計算一個串列*所有的*劃分？
可能的方式有很多，其中一種思路如下。首先，空串列 |[]| 只有一個可能的劃分，即是 |[]|.
考慮 |x:xs|, 如果 |xs| 已經被劃分完畢，對於 |x| 我們有兩個選擇：讓它成為單獨的串列，
或著將 |xs| 加入最左邊的串列。
寫成歸納定義如下：
```haskell
parts :: List a -> List (List (List a))
parts []      = [[]]
parts (x:xs)  = concat (map (extend x) (parts xs)) {-"~~,"-}
  where  extend x []        = [[[x]]]
         extend x (ys:yss)  = [[x]:ys:yss, (x:ys):yss] {-"~~."-}
```
{.nobreak}遞迴呼叫 |parts xs| 找出 |xs| 的所有劃分，
輔助函數 |extend x :: List (List a) -> List (List (List a))| 則作用在其中一個劃分上。
我們得分出兩個狀況：

  1. 如果該劃分含第一個串列 |ys| 和剩下的 |yss|, 我們可選擇讓 |x| 自成一個串列，或著加入 |ys| 中。
     我們把這兩種選擇收集到一個串列中，因此 |extend| 的結果有三層 |List|。
  2. 如果該劃分是空的，加入 |x| 的劃分必定是 |[[x]]|，但仍需放入一個串列中，表示「只有這一個選擇」。

{.nobreak}呼叫 |map (extend x)| 的結果需再用一個 |concat| 聯集在一起。

:::{.infobox title="反函數"}
```texonly
%{
%format inv f = f "^{-1}"
```
假設我們有一個取反函數的運算元：給定 |f :: a -> b|, 其反函數 |inv f| 的型別是 |b -> List a|。
|inv f y| 將所有使得 |f x = y| 的 |x| 收集在串列中。
則 |parts| 可以有一個更接近本節中文字描述的定義：
```spec
  parts = filter (all (not . null)) . inv concat {-"~~."-}
```
{.nobreak}計算 |parts xs| 時，我們用 |inv concat| 找出所有滿足 |concat yss = xs| 的 |List (List a)|, 並且只挑出不含空串列的。

上述定義可以轉換成本節的歸納定義。相關研究可參考 @MuBird:03:Theory.
```texonly
%}
```
:::


## 再談「讓符號為你工作」 {#sec:using-hints-from-symbols}

看了這麼多歸納定義，我們做個較複雜的練習，並以此為例再談談「讓符號為你工作」。
本節在初次閱讀時可略過。

以下的函數 |ins| 將一個元素插到一個串列的空隙中。它和第\@ref{sec:fan-perm}節中的 |fan| 類似但稍有不同 --- |ins x xs| 不會把 |x| 放到 |xs| 的結尾。
^[本節不使用 |fan| 而另外定義了 |ins| 的原因僅是因為如此使得性質 \@eqref{eq:append-ins} 較單純而方便說明。]
例如：|ins 1 [2,3,4] = [[1,2,3,4],[2,1,3,4],[2,3,1,4]]|。
```haskell
ins :: a -> List a -> List (List a)
ins x []      = []
ins x (y:ys)  = (x:y:ys) : map (y:) (ins x ys) {-"~~."-}
```
{.nobreak}請證明對所有 |x|, |ys|, 與 |zs|,
```{.equation #eq:append-ins}
  |map (++zs) (ins x ys) ++  map (ys++) (ins x zs)| &= |ins x (ys ++ zs) {-"~~."-}|
```
{.nobreak}意即：在 |ys ++ zs| 之中插入 |x| 的所有方法，
是 1. 把 |x| 插入 |ys| 之中，並把每個結果的右邊接上 |zs|,
以及 2. 把 |x| 插入 |zs| 之中，並把每個結果的左邊接上 |ys|.

面對一個如此冗長的式子，我們該如何著手？我們可猜想如此複雜的性質大概會需要歸納證明。
但在哪個變數上做歸納呢？
觀察\@eqref{eq:append-ins}，等號左手邊最外側的運算子是|(++)|。
計算 |(++)| 時，根據定義，先被樣式配對的是 |(++)| 左邊的參數，也就是 |map (++zs) (ins x ys)|。
再來，根據 |map| 的定義，|map (++zs) (ins x ys)| 的運算要有進展，得先把 |ins x ys| 算出來。
最後，根據 |ins| 的定義，計算 |ins x ys| 會先拆開 |ys|.
由此可知，等號左手邊的運算是從拆解 |ys| 開始的。
等號右手邊的情況也一樣：根據 |ins| 與 |(++)| 的定義，要計算 |ins x (ys ++ zs)|，第一個被拆開的是 |ys|. 因此，欲證明\@eqref{eq:append-ins}，合理的猜測是在 |ys| 上做歸納！

```texonly
% Induction on |ys|. For |ys := []| we have
% ```spec
%       map (++zs) (ins x []) ++ map ([] ++) (ins x zs)
%  ===    {- definition of |map|, |ins|, and |(++)| -}
%       map ([] ++) (ins x zs)
%  ===    {- since |([] ++) = id| and |map id xs = xs| -}
%       ins x zs
%  ===    {- definition s of |(++)| -}
%       ins x ([] ++ zs) {-"~~."-}
% ```
```

我們省略 |ys := []| 的情況，僅考慮歸納情況 |ys := y:ys|。
經代換後的式子是 |map (++zs) (ins x (y:ys)) ++ map ((y:ys) ++) (ins x zs)|.
我們採取的策略和證明定理\@ref{thm:exp-plus-times}時一樣：
*想辦法湊出 |map (++zs) (ins x ys) ++  map (ys++) (ins x zs)|, 以便使用歸納假設*。
由此論證如下（步驟加上編號以利說明）：
```{.haskell .invisible}
insCat :: a -> a -> List a -> List a -> List (List a)
insCat x y ys zs =
```
```haskell
     map (++zs) (ins x (y:ys)) ++ map ((y:ys) ++) (ins x zs)
 ===     {- 1. |ins| 與 |map| 之定義 -}
     (x:y:ys++zs) : map (++zs) (map (y:) (ins x ys)) ++ map ((y:ys) ++) (ins x zs)
 ===     {- 2. |map| 融合 -}
     (x:y:ys++zs) : map ((++zs) . (y:)) (ins x ys) ++ map ((y:ys) ++) (ins x zs)
 ===     {- 3. 由於 |(++zs) . (y:) = (y:) . (++zs)| (習題 \ref{ex:append-cons}) -}
     (x:y:ys++zs) : map ((y:) . (++zs)) (ins x ys) ++ map ((y:ys) ++) (ins x zs)
 ===     {- 4. |map| 融合 -}
     (x:y:ys++zs) : map (y:) (map (++zs) (ins x ys)) ++ map ((y:ys) ++) (ins x zs)
 ===     {- 5. 由於 |((y:ys)++) = (y:).(ys++)| (習題 \ref{ex:cons-append}) -}
     (x:y:ys++zs) : map (y:) (map (++zs) (ins x ys)) ++ map ((y:).(ys++)) (ins x zs)
 ===     {- 6. |map| 融合 -}
     (x:y:ys++zs) : map (y:) (map (++zs) (ins x ys)) ++ map (y:) (map (ys++) (ins x zs))
 ===     {- 7. 由於 |map f (xs ++ ys) = map f xs ++ map f ys| -}
     (x:y:ys++zs) : map (y:) (map (++zs) (ins x ys) ++ map (ys++) (ins x zs))
 ===     {- 8. 歸納假設 -}
     (x:y:ys++zs) : map (y:) (ins x (ys ++ zs))
 ===     {- 9. |ins| 與 |(++)| 之定義 -}
     ins x ((y:ys)++zs) {-"~~."-}
```
{.nobreak}雖然步驟多、式子長，但策略確定後，整個證明的架構便很清楚。第 1 到 7 步都是為了可在第 8 步使用歸納而做的準備。
為湊出 |map (++zs) (ins x ys) ++ map (ys++) (ins x zs)|, 第 2 至第 4 步把 |map (++zs)| 往裡推，把第一個 |map (y:)| 往外提；第 5, 6 步則提出另一個 |map (y:)|。式子變成 |map (y:) ... ++ map (y:) ...| 的形式後，共同的 |map (y:)| 可在第 7 步提出來。
如此，終於可使用歸納假設了。
*整個證明中，要配對哪個變數、把式子中的哪些項往哪兒移動，都被符號引導著而有線索可循。*
證明中用到的兩個性質 |(++zs) . (y:) = (y:) . (++zs)| 與 |((y:ys)++) = (y:).(ys++)| 並非天外飛來，而是確立了目標後，因為有需求（兩者分別讓我們把 |(++zs)| 與 |(ys++)| 往右推，把 |(y:)| 往左拉）而設計出並另外證明的性質。

初學者常犯的一個錯誤是：以為所有情況下、所有的變數都需要樣式配對。
事實上，*過度的樣式配對是形式證明中希望避免的*。
藉由觀察 \@eqref{eq:append-ins}，我們決定對 |ys| 做歸納，證明過程中發現如此便已經足夠。
如果我們對 |ys| 和 |zs| 都做配對，將必須處理四種情況：|ys,zs := [],[],[]|, |ys,zs := [],z:zs|, |ys,zs := [],z:zs| |ys,zs := y:ys,z:zs|。一個待證明的性質若有 |n| 個串列，似乎得分出 $2^n$ 種情況 --- 只有萬不得已我們才會這麼做。

最嚴重的問題並不是情況數目太多，而是過度的樣式配對破壞了證明的結構。
如果對 |zs| 做配對，許多人會很自然地想把 |ins x (z:zs)| 展開。
證明可能如此進行：
```{.haskell .invisible}
insCat' :: a -> a -> a -> List a -> List a -> List (List a)
insCat' x y z ys zs =
```
```haskell
   map (++(z:zs)) (ins x (y:ys)) ++ map ((y:ys) ++) (ins x (z:zs))
 ===   {- 將 |(++)| 的左手邊展開 -}
   (x:y:ys++(z:zs)) : map (++(z:zs)) (map (y:) (ins x ys)) ++
     map ((y:ys) ++) (ins x (z:zs))
 ===   {- 展開 |ins x (z:zs)| -}
   (x:y:ys++(z:zs)) : map (++(z:zs)) (map (y:) (ins x ys)) ++
     map ((y:ys) ++) ((x:z:zs) : map (z:) (ins x zs))
 ===   {- |map| 的定義 -}
   (x:y:ys++(z:zs)) : map (++(z:zs)) (map (y:) (ins x ys)) ++
     ((y:ys ++ (x:z:zs)) : map ((y:ys) ++) (map (z:) (ins x zs))) {-"~~."-}
```
{.nobreak}要從這樣的式子中再整理出
|map (++(z:zs)) (ins x (y:ys)) ++ map ((y:ys) ++) (ins x (z:zs))|
以便做歸納假設，
我們得看出如何把（本來不需展開的）|ins x (z:zs)| 給收回來。
式子的結構已經被破壞，操作起來的難度便大大提高了。
^[這其實是我於 2019 年開設的程式語言課程的期末考題。在十數位將 |ins x (z:zs)| 展開的同學中，只有一位成功地將它收了回來。]

:::{.exlist}
:::{.exer #ex:cons-append}
證明：對所有 |y| 與 |ys|, |(y:).(ys++) = ((y:ys)++)|.
:::
:::{.exans .compact}
```spec
   ((y:).(ys++)) xs
=   {- definition of |(.)| -}
   y : (ys ++ xs)
=   {- definition of |(++)| -}
   (y : ys) ++ xs {-"~~."-}
```
:::
:::{.exer #ex:append-cons}
證明：對所有 |y| 與 |zs|, |(++zs) . (y:) = (y:) . (++zs)|.
以上兩者都是不需歸納、也不須狀況分析的單純證明。
:::
:::{.exans .compact}
```spec
  ((++zs) . (y:)) xs
=   {- definition of |(.)| -}
  (++zs) (y:xs)
= (y:xs) ++ zs
=   {- definition of |(++)| -}
   y :(xs ++ zs)
=  (y:) ((++ zs) xs)
=   {- definition of |(.)| -}
   ((y:) . (++zs)) xs {-"~~."-}
```
:::
:::



## 其他歸納資料結構 {#sec:other-inductive-datatypes}

不僅自然數與串列，歸納式的函數定義與證明可用在所有歸納定義的資料結構上。
以第\@ref{sec:user-defined-data}節提及的兩種二元樹為例：
```spec
data ITree a  = Null | Node a (ITree a) (ITree a) {-"~~,"-}
data ETree a  = Tip a | Bin (ETree a) (ETree a) {-"~~."-}
```
{.nobreak}型別 |ETree| 可讀解為一個歸納資料結構，我們可在它之上以歸納法定義函數。
例如，下述的函數 |minE| 計算一個 |ETree| 中最小的元素，|mapE f| 則將函數 |f| 作用在樹中的每個元素上。
```haskell
minE :: ETree Int -> Int
minE (Tip x)    = x
minE (Bin t u)  = minE t `min` minE u {-"~~,"-}

mapE :: (a -> b) -> ETree a -> ETree b
mapE f (Tip x)    = Tip (f x)
mapE f (Bin t u)  = Bin (mapE f t) (mapE f u) {-"~~."-}
```
{.nobreak}我們也有如下的歸納原則：
```{.equation title="ETree 上之歸納法："}
  |(forall t :: ETree a . P t) {-"~"-}<== {-"~\\\qquad"-}|
  |(forall x . P (Tip x)) && (forall t u . P (Bin t u) <== P t && P u) {-"~~."-}|
```

作為例子，我們證明下列性質：
```spec
  minE (mapE (x +) t) = x + minE t {-"~~."-}
```
{.nobreak}左手邊將樹中的每個元素都加上 |x|, 然後取最小的。右手邊則告訴我們不必這麼麻煩，先取最小的，再加上 |x| 即可！
:::{.proof}
基底狀況 |t := Tip y| 很容易成立。至於歸納狀況 |t := Bin t u|,
使其成立的關鍵性質是加法可分配至 |(`min`)| 中：|x + (y `min` z) = (x+y) `min` (x+z)|:
```{.haskell .invisible}
minEmapEplusPf1 x t u =
```
```haskell
    minE (mapE (x +) (Bin t u))
 ===   {- |mapE| 與 |minE| 之定義 -}
    minE (mapE (x+) t) `min` minE (mapE (x+) u)
 ===   {- 歸納假設 -}
    (x + minE t) `min` (x + minE u)
 ===   {- 算術：加法分配至 |(`min`)| 中 -}
    x + (minE t `min` minE u)
 ===   {- |minE| 之定義 -}
    x + minE (Bin t u) {-"~~."-}
```
:::

:::{.exlist}
:::{.exer #ex:ITree-principle}
請寫出 |ITree| 的歸納原則？
:::
:::{.exans .compact}
```{.equation title="ITree 上之歸納法："}
  |(forall t :: ITree a . P t) {-"~"-}<== {-"~\\\qquad"-}|
    |(P Null && (forall x t u . P (Node x t u) <== P t && P u) {-"~~."-}|
```
:::
:::{.exer #ex:ITree-mapI}
定義函數 |mapI :: (a -> b) -> ITree a -> ITree b|, 使得 |mapI f| 則將函數 |f| 作用在樹中的每個元素上。
:::
:::{.exans .compact}
```haskell
mapI :: (a -> b) -> ITree a -> ITree b
mapI f Null          = Null
mapI f (Node x t u)  = Node (f x) (mapI f t) (mapI f u) {-"~~."-}
```
:::
:::{.exer #ex:ITree-tags}
試定義函數 |tags :: ITree a -> List a|, 由左至右傳回給定之 |ITree| 的所有標籤。例如，若
```spec
  t = Node 3  (Node 2 (Node 1 Null Null) Null)
              (Node 5  (Node 4 Null Null)
                       (Node 6 Null Null)) {-"~~,"-}
```
{.nobreak}則 |tags t = [1,2,3,4,5,6]|.
:::
:::{.exans .compact}
```haskell
tags :: ITree a -> List a
tags Null          = []
tags (Node x t u)  = tags t ++ [x] ++ tags u {-"~~."-}
```
:::
:::{.exer #ex:ITree-size}
試定義函數 |size :: ITree a -> Int|, 傳回給定的 |ITree| 之標籤數目 --- 例如 |size Null = 0|, |size (Node 3 Null (Node 4 Null Null)) = 2|.
:::
:::{.exans .compact}
```haskell
size :: ITree a -> Nat
size Null          = Zero
size (Node x t u)  = Suc (size t +: size u) {-"~~."-}
```
:::
:::{.exer #ex:ITree-length-size}
接續前兩題，證明 |length (tags t) = size t|.
:::
:::{.exans}
在 |t| 之上做歸納。當 |t := Null|，顯然等號兩邊都歸約為 |0|.
當 |t := Node x t u|:
```{.haskell .invisible}
lenLeavesPf1 x t u =
```
```haskell
      length (tags (Node x t u))
 ===    {- |length| 與 |leaves| 之定義 -}
      Suc (length (tags t) +: length (tags u))
 ===    {- 歸納假設 -}
      Suc (size t +: size u)
 ===    {- |size| 之定義 -}
      size (Node x t u) {-"~~."-}
```
:::
:::

## 由集合論看歸納法 {#sec:induction-set-theory}

歸納證明為何成立？本節試圖以集合論的角度理解歸納法，試圖建立幾個觀念：當我們說某型別是「歸納定義」的，常常代表它是具有某個結構的最小集合。而歸納證明可以理解為證明某型別是所有滿足某性質的事物的子集。本節於初次閱讀時可跳過。

{title="序理論回顧"} 為了本章的完整性，我們在這兒回顧一些重要定義。
對學過序理論或抽象代數的讀者來說，以下概念應不陌生。
如果您還不熟悉這些定義，由於它們在程式語言語意中常常使用，值得花些時間弄懂。
:::{.definition title="前序、偏序" #def:preorder}
給定集合$S$, 令 $(\leq)$ 為 $S$ 上的一個二元關係。如果 $(\leq)$ 滿足：

  * *自反律*：對所有 $x \in S$, |x <= x|.\index{reflexivity 自反律}
  * *遞移律*：對所有 $x,y,z \in S$, |x <= y && y <= z ==> x <= z|,\index{transitivity 遞移律}

則 $(\leq)$ 被稱為$S$ 上的一個*前序*(*preorder*).
\index{preorder 前序}
如果 $(\leq)$ 除上述兩性質外還滿足：

  * *反對稱律*：對所有 $x,y \in S$, |x <= y && y <= x ==> x = y|.

則 $(\leq)$ 被稱為$S$ 上的一個*偏序*(*partial order*).
\index{partial order 偏序}
如果 $S$ 上有偏序 $(\leq)$, 我們常把它們放在一起，稱 $(S,(\leq))$ 為一個*偏序集合*(*partially ordered set*, 或 *poset*).
\index{partially ordered set 偏序集合}
\index{poset 偏序集合}

:::

:::{.definition title="最小上界、最大下界" #def:min-max-bound}
給定偏序集合 $(S,(\leq))$，考慮其子集 $T \subseteq S$:

  * 如果 $x \in S$ 滿足 $(\forall y \in T: y \leq x)$, 則 $x$ 是 $T$ 的一個*上界*(*upper bound*).
    \index{upper bound 上界}
  * 如果 $T$ 的所有上界中存在「最小」的，該值稱作 $T$ 的*最小上界*(*supremum*, 或 *least upper bound*), 記為 $\Varid{sup}~T$.
    \index{supremum 最小上界}
    \index{least upper bound 最小上界}
    依據定義，$\Varid{sup}~T$ 滿足 $(\forall y \in T: y \leq x) \Rightarrow \Varid{sup}~T \leq x$.
  * 如果 $x \in S$ 滿足 $(\forall y \in T: y \geq x)$, 則 $x$ 是 $T$ 的一個*下界*(*lower bound*).
    \index{lower bound 下界}
  * 如果 $T$ 的所有下界存在「最大」的，該值稱作 $T$ 的*最大下界*(*infimum*, 或*greatest lower bound*), 記為 $\Varid{inf}~T$.
    \index{infimum 最大下界}
    \index{greatest lower bound 最大下界}
    依據定義，$\Varid{inf}~T$ 滿足 $(\forall y \in T: y \geq x) \Rightarrow \Varid{inf}~T \geq x$.



:::

:::{.definition title="格、完全格" #def:lattice}
考慮偏序集合 $(S,(\leq))$:

  * 如果對任何 $x, y \in S$, |sup {x,y}| 和 |inf {x,y}| 均存在且都在 $S$ 之中，則 $(S,(\leq))$ 是一個格 (lattice)。
    \index{lattice 格}
  * 如果對任何 $T \subseteq S$，$\Varid{sup}~T$ 和 $\Varid{inf}~T$ 均存在且都在 $S$ 之中，則 $(S,(\leq))$ 是一個完全格 (complete lattice)。
    \index{complete lattics 完全格}


:::

在本節之中我們只會考慮一種格。令 $D$ 代表所有範式（如 |Zero|, |Suc Zero|, |True|, |1 : 2 : []|, |(\x -> x)|...）的集合，我們考慮的格是 ${\cal P}D$，即 $D$ 的所有子集形成的集合。其上的偏序就是子集關係 $(\subseteq)$.


{title="定點"} 再回顧一些與*定點*相關的理論。
:::{.definition title="定點" #def:fixed-point}
給定完全格 |(A, (<=))| 和函數 |f :: A -> A|,

  1. 如果 |f x <= x|, 我們說 |x| 是 |f| 的一個*前定點* (*prefixed point*).
     \index{fixed point 定點!prefixed point 前定點}
  2. 如果 |f x = x|, 我們說 |x| 是 |f| 的一個*定點* (*fixed point*).\index{fixed point 定點}
  3. 如果 |f x >= x|, 我們說 |x| 是 |f| 的一個*後定點* (*postfixed point*).


:::


:::{.definition title="最小前定點、最大後定點" #def:mu-nu}
給定完全格 |(A, (<=))| 和函數 |f :: A -> A|,

  * 如果 |f| 的前定點之中存在最小值，我們將它記為 |mu f|.
    根據此定義，|mu f| 滿足 |f x <= x ==> mu f <= x|.
    \index{least prefix point 最小前定點}
  * 如果 |f| 的後定點之中存在最大值，我們將它記為 |nu f|.
    根據此定義，|nu f| 滿足 |x <= f x ==> x <= nu f|.
    \index{greatest postfix point 最大後定點}


:::

:::{.theorem #thm:f-muf}
給定完全格 |(A, (<=))| 和函數 |f :: A -> A|,

  * |f| 的最小前定點 |mu f| 也是最小的定點，
  * |f| 的最小前定點 |nu f| 也是最大的定點。


:::


{title="歸納定義"} 回顧自然數的定義：
```spec
  data Nat = Zero | Suc Nat {-"~~."-}
```
{.nobreak}第\@ref{sec:math-induction}節對這行定義的解釋是：

  1. |Zero| 的型別是 |Nat|;
  2. 如果 |n| 的型別是 |Nat|, |Suc n| 的型別也是 |Nat|;
  3. 此外，沒有其他型別是 |Nat| 的東西。

{.nobreak}如果我們把一個型別視作一個集合，上述條件定出了怎麼樣的集合呢？
^[請注意：「把型別視為集合」僅在簡單的語意之中成立。本書後來將會討論更複雜的語意，屆時型別並不只是集合。]
用 |Nat| 表示我們定出的這個新型別。上述第 1.點告訴我們 |Zero| 是 |Nat| 的成員，也就是 |{Zero} `sse` Nat|. 第 2.點則表示，從 |Nat| 這個集合中取出任一個元素 |n|, 加上 |Suc|, 得到的結果仍會在 |Nat| 之中。也就是說 |{Suc n || n `mem` Nat} `sse` Nat|. 集合基本定理告訴我們 |X `sse` Z && Y `sse` Z| 和
|X `union` Y `sse` Z| 是等價的，所以：
^[|X `sse` Z && Y `sse` Z <=> X `union` Y `sse` Z| 被稱為「|(`union`)| 的泛性質」。]
```{.equation #eq:Nat-Ind-0}
    |{Zero} `union` { Suc n || n `mem` Nat }| & ~\subseteq~ |Nat| \mbox{~~.}
```
{.nobreak}意思是說，如果我們定義一個*集合到集合*的函數 |NatF|:
```spec
  NatF X = {Zero} `union` { Suc n | n `mem` X } {-"~~,"-}
```
{.nobreak}那麼 \@eqref{eq:Nat-Ind-0} 可以改寫為
```equation
   |NatF Nat| &~\subseteq~ |Nat| \mbox{~~,}
```
{.nobreak}也就是說，|Nat| 是 |NatF| 的一個前定點！

至於 3.呢？它告訴我們 |Nat| 僅含恰巧能滿足 1.和 2.的元素，沒有多餘。
意即，|Nat| 是*滿足 1.和 2.的集合之中最小的*。
若有另一個集合 |Z| 也滿足 1.和 2., 我們必定有 |Nat `sse` Z|.
也就是說 |Nat| 是 |NatF| 的最小前定點：|Nat = mu NatF|!

給定述語|P|, 我們把所有「滿足 |P| 的值形成的集合」也記為 |P|.
^[對任何 |A|, 函數 |P :: A -> Bool| 和「滿足 |P| 的 |A| 形成的集合」是同構的。我們可把它們等同視之。]
數學歸納法的目的是證明所有自然數都滿足 |P|。
但，「所有自然數都滿足 |P|」其實就是 |Nat `sse` P|.

如何證明 |Nat `sse` P|? 如前所述，|Nat| 是 |NatF| 的最小前定點。
如果 |P| 恰巧也是 |NatF| 的一個前定點，|Nat `sse` P| 一定得成立。
寫成推論如下：
```spec
    Nat `sse` P
<==   {- |Nat| 是 |NatF| 的最小前定點，定義\ref{def:mu-nu} -}
    NatF P `sse` P
<=>   {- |NatF| 的定義 -}
    {Zero} `union` {Suc n | n `mem` P} {-"~"-}`sse` {-"~"-} P
<=>   {- |(`union`)| 的泛性質：|X `union` Y `sse` Z {-"~"-}<=>{-"~"-} X `sse` Z && Y `sse` Z| -}
    {Zero} `sse` P {-"~"-}&&{-"~"-} {Suc n | n `mem` P} `sse` P {-"~~."-}
```
{.nobreak}也就是說，如果證出|{Zero} `sse` P| 和 |{Suc n || n `mem` P} `sse` P|，我們就有 |Nat `sse` P|。其中，

  1. |{Zero} `sse` P| 翻成口語便是「|P| 對 |Zero| 成立」，
  2. |{Suc n || n `mem` P} `sse` P| 則是「若 |P| 對 |n| 成立，|P| 對 |Suc n| 亦成立」。

{.nobreak}正是數學歸納法的兩個前提！

原來，*數學歸納法之所以成立，是因為自然數被定義為某函數的最小前定點*。
事實上，當我們說某型別是「歸納定義」的，意思便是它是某個函數的最小前定點。

以串列為例。為單純起見，先考慮元素皆為 |Nat| 的串列。
如下的定義
```texonly
%%format ListNat = "{\Varid{List}\mathbb{N}}"
%%format ListNatF = "{\Varid{List}\mathbb{N}\Varid{F}}"
```
```spec
data ListNat {-"~\,"-}={-"~\,"-} [] {-"~"-}|{-"~"-} Nat : ListNat {-"~~,"-}
```
{.nobreak}可理解為 |ListNat = mu ListNatF|，而 |ListNatF| 定義為：
```spec
  ListNatF X = { [] } `union` { n : xs | xs `mem` X, n `mem` Nat  } {-"~~."-}
```
{.nobreak}至於如下定義的、有型別參數的串列，
```spec
data List a {-"~\,"-}={-"~\,"-} [] {-"~"-}|{-"~"-} a : List a {-"~~,"-}
```
{.nobreak}則可理解為 |List a = mu(ListF a)| --- |List a| 是 |ListF a| 的最小前定點，其中 |ListF| 定義如下：
```spec
  ListF A X = { [] } `union` { x : xs | xs `mem` X, x `mem` A } {-"~~."-}
```
{.nobreak}給定某型別 |A|, 當我們要證明某性質 |P| 對所有 |List A| 都成立，實質上是想要證明 |List A `sse` P| （同樣地，此處 |P| 代表所有使述語 |P| 成立的值之集合）。我們推論如下：
```spec
  List A `sse` P
<==   {- |List a = mu(ListF a)| -}
  ListF A P `sse` P
<=>   {- |ListF| 之定義 -}
  { [] } `union` { x : xs | xs `mem` P, x `mem` A } `sse` P
<=>   {- |(`union`)| 的泛性質 -}
  {[]} `sse` P  {-"~"-}&&{-"~"-} { x : xs | xs `mem` P, x `mem` A } `sse` P {-"~~."-}
```
{.nobreak}其中 |{[]} `sse` P| 翻成口語即是「|P []| 成立」；
|{ x : xs || xs `mem` P, x `mem` A } `sse` P| 則是
「若 |P xs| 成立，對任何 |x::A|, |P (x:xs)| 成立」。

我們之所以能做自然數與串列的歸納證明，因為它們都是歸納定義出的型別 ---
它們都被定義成某函數的最小前定點。若非如此，歸納證明就不適用了。
那麼，有不是歸納定義出的型別嗎？

讀者可能注意到，本節起初同時談到最小前定點與最大後定點，但後來只討論了前者。
事實上，我們也可以把一個資料型別定義為某函數的最大後定點。
這時我們說該資料型別是個*餘歸納*(*coinductive*)定義，如此訂出的型別稱為*餘資料*(*codata*)。
\index{coinduction 餘歸納}\index{codata 餘資料}
歸納定義出的資料結構是有限的，而餘歸納定義的型別可能包括無限長的資料結構。
寫餘資料相關的證明，另有一套稱作餘歸納(coinduction)的方法，
而餘歸納也影響到我們如何寫與餘資料相關的程式。
餘歸納和歸納的相關理論剛好是漂亮的對偶。我們將在 \todo{where} 介紹餘歸納。

:::{.exlist}
:::{.exer #ex:ITree-ETree-mu}
回顧第\@ref{sec:user-defined-data}節中介紹的兩種樹狀結構：
```spec
data ITree a  = Null | Node a (ITree a) (ITree a) {-"~~,"-}
data ETree a  = Tip a | Bin (ETree a) (ETree a) {-"~~."-}
```
{.nobreak}說說看它們分別是什麼函數的最小前定點，並找出它們的歸納原則。
:::
:::

## 歸納定義的簡單變化 {#sec:induction-variations}

目前為止，我們所認定「良好」的函數定義是這種形式：
```spec
f Zero     = ...
f (Suc n)  = ... f n ...
```
{.nobreak}我們知道這樣定義出的函數是個全函數、對所有輸入都會終止、和歸納法有密切關係...。
以後的幾個章節中，我們將逐步放鬆限制，允許更有彈性的函數定義模式。
我們先從歸納法的一些較簡單的變化開始。

```texonly
%{
%format f1
%format fb = "\Varid{f}_{\Varid{b}}"
%format NatP = Nat"^{+}"
%format One = "\mathbf{1}"
```

{title="基底狀況的變化"}
有些函數的值域是「正整數」或「大於 b 的整數」。
定義這些函數時我們可用這樣的模式：
```spec
f1 One      = e                                   fb b        = e
f1 (Suc n)  = ... f1 n ... {-"~~,\qquad\qquad"-}  fb (Suc n)  = ... fb n ... {-"~~."-}
```
{.nobreak}我們可把 |f1| 理解為：另外訂了一個資料型別 |data NatP = One || Suc NatP|,
以 |One| 為基底狀況，而 |f1| 是 |NatP| 之上的全函數。|fb| 的情況也類似。
與使用 |Nat| 的函數混用時，我們就得在這兩個型別之間作轉換。這相當於檢查給 |f1| 的輸入都是大於 |1| 的整數。實務上為了方便，我們仍用同一個型別實作 |Nat| 與 |NatP|, 就如同實務上用 |Int| 實作 |Nat| 一樣。

串列的情形也類似。有些函數若能只定義在「不是空的串列」上，其定義會比較合理。
對於這些函數，我們可想像有這麼一個「非空串列」資料型別
|data ListP a = [a] || a : ListP a|，
只是為了方便，我們用普通串列實作它。
^[在一些型別系統更強大的語言中、進行更注重證明的應用時，我確實有將 |NatP| 與 |ListP| 做成與 |Nat| 和 |List| 不同的型別的經驗與需求。]

:::{.example #ex:maximumP}
假設 |x `max` y| 傳回 |x| 與 |y| 中較大的值。
函數 |maximumP| 傳回一個非空串列中的最大元素：
```haskell
maximumP :: ListP Int -> Int
maximumP [x]     = x
maximumP (x:xs)  = x `max` maximumP xs {-"~~."-}
```
{.nobreak}Haskell 標準函式庫中另有一個函數 |maximum :: List Int -> Int|, 但該函數需假設 |Int| 中有一個相當於 $-\infty$ 的值存在，以便當作 |maximum []| 的結果：
```spec
maximum []      = -infty
maximum (x:xs)  = x `max` maximum xs {-"~~."-}
```
:::
```texonly
% %format initsP = "\Varid{inits}^{+}"
% \begin{exlist}
% \Exercise 定義 |initsP|, 傳回
% \Answer ~~\\
% ```spec
% initsP [x]    = [[x]]
% initsP (x:xs) = [x] : map (x:) (initsP xs)
% ```
% \end{exlist}
```
```texonly
%}
```

:::{.example #ex:partsP}
回顧第\@ref{sec:fan-perm}節提及的「劃分(partition)」：如果 |concat yss = xs|, 且|yss| 中的每個串列都不是空的，則 |yss| 是 |xs| 的一個劃分。
\index{partition 劃分}
如果我們限定 |xss| 為非空串列，計算所有劃分的函數
|partsP :: ListP a -> List (ListP (ListP a))| 可以寫得更簡潔：
```haskell
partsP [x]     = [[[x]]]
partsP (x:xs)  = concat (map (extend x) (partsP xs)) {-"~~,"-}
  where extend x (ys:yss) = [[x]:ys:yss, (x:ys):yss] {-"~~."-}
```
{.nobreak}由於每個劃分一定是非空串列，|extend| 不需考慮輸入為 |[]| 的情況。
:::

{title="多個參數的歸納定義"}
函數 |take|/|drop| 的功能與 |takeWhile|/|dropWhile| 很類似，
但其定義方式卻有些不同：
```haskell
take :: Nat -> List a -> List a
take Zero     xs      = []
take (Suc n)  []      = []
take (Suc n)  (x:xs)  = x : take n xs {-"~~,"-}

drop :: Nat -> List a -> List a
drop Zero     xs      = xs
drop (Suc n)  []      = []
drop (Suc n)  (x:xs)  = drop n xs {-"~~."-}
```
{.nobreak}我們可把 |take|/|drop| 想成在自然數上歸納定義成的高階函數：
|take (Suc n)| 的值是一個 |List a -> List a| 的函數。
定義 |take (Suc n)| 時，我們假設 |take n| 已有定義。
唯一的特殊處是我們另分出兩個子情況：串列為 |[]|, 或串列為 |x:xs|.

根據「使證明的結構符合程式的結構」的原則，如果要做關於
|take|/|drop| 的證明，一種可能做法是也依循著它們的結構：
先拆解自然數，在 |n := Suc n| 的情況中再分析串列的值。
作為例子，我們來驗證第\@pageref{eq:taken-dropn}頁提到的這個性質：
:::{.theorem #thm:take-drop-id}
對所有 |n| 與 |xs|, |take n xs ++ drop n xs = xs|.
:::
:::{.proof}
在 |n| 上做歸納。在 |n := []| 的情況下，等號兩邊都化簡為 |[]|.
在 |n:=Suc n| 的情況中，我們再細分出兩種情形：

{.nobreak}**狀況** |n := Suc n|, |xs := []|. 顯然等號兩邊都化簡為 |[]|.

{.nobreak}**狀況** |n := Suc n|, |xs := x:xs|:
```spec
   take (Suc n) (x:xs) ++ drop (Suc n) (x:xs)
=    {- |take| 與 |drop| 之定義 -}
   x : take n xs ++ drop n xs
=    {- 歸納假設 -}
   x : xs {-"~~."-}
```
:::



然而，本章討論的是所有資料結構都是歸納定義、所有函數也都是全函數的世界。
如果我們的世界中有不終止程式存在，上式便不見得成立了。

:::{.exlist}
:::{.exer #ex:take-drop-non-termination}
請舉一個在允許不終止程式的 Haskell 中，
|take n xs ++ drop n xs = xs| 不成立的例子。
:::
:::{.exer #ex:head-tail-id-neg}
對任何串列 |xs|，|head xs : tail xs = xs| 都成立嗎？請舉一個反例。
:::
:::{.exans}
|head [] : tail [] /= []|.
:::
:::{.exer #ex:take-take}
證明對自然數 |m|, |n|, |take m (take (m+n) xs) = take m xs|.
:::
:::{.exans}
針對 |m| 做歸納。當 |m := Zero|, 等號兩邊都歸約成 |[]|。
考慮|m := Suc m|. 此時針對 |xs| 做分析。
當 |xs := []|, 等號兩邊亦都歸約成 |[]|。
考慮 |xs := x:xs| 的情況：
```{.haskell .invisible}
takeTakePf1 :: Nat -> Nat -> a -> List a -> List a
takeTakePf1 m n x xs =
```
```haskell
      take (Suc m) (take (Suc m +: n) (x:xs))
 ===    {- |(+:)| 與 |take| 之定義 -}
      take (Suc m) (x : take (m +: n) xs)
 ===    {- |take| 之定義 -}
      x : take m (take (m +: n) xs)
 ===    {- 歸納假設 -}
      x : take m xs
 ===    {- |take| 之定義 -}
      take (Suc m) xs {-"~~."-}
```
:::
:::{.exer #ex:drop-take}
證明對自然數 |m|, |n|, |drop m (take (m +: n) xs) = take n (drop m xs)|.
:::
:::{.exans}
針對 |m| 做歸納。當 |m := Zero|, 等號兩邊都歸約成 |take n xs|。
考慮|m := Suc m|. 此時針對 |xs| 做分析。
當 |xs := []|, 等號兩邊亦都歸約成 |[]|。
考慮 |xs := x:xs| 的情況：
```{.haskell .invisible}
dropTakePf1 :: Nat -> Nat -> a -> List a -> List a
dropTakePf1 m n x xs =
```
```haskell
      drop (Suc m) (take (Suc m +: n) (x:xs))
 ===    {- |(+:)| 與 |take| 之定義 -}
      drop (Suc m) (x : take (m +: n) xs)
 ===    {- |take| 之定義 -}
      drop n (take (m +: n) xs)
 ===    {- 歸納假設 -}
      take n (drop m xs)
 ===    {- |take| 之定義 -}
      take n (drop (Suc m) (x:xs)) {-"~~."-}
```
:::
:::{.exer #ex:drop-drop}
證明對自然數 |m|, |n|, |drop (m +: n) xs) = drop n (drop m xs)|.
:::
:::{.exans}
針對 |m| 做歸納。當 |m := Zero|, 等號兩邊都歸約成 |drop n xs|。
考慮|m := Suc m|. 此時針對 |xs| 做分析。
當 |xs := []|, 等號兩邊亦都歸約成 |[]|。
考慮 |xs := x:xs| 的情況：
```{.haskell .invisible}
dropDropPf1 :: Nat -> Nat -> a -> List a -> List a
dropDropPf1 m n x xs =
```
```haskell
      drop (Suc m +: n) (x:xs)
 ===    {- |(+:)| 與 |take| 之定義 -}
      drop (m +: n) xs
 ===    {- 歸納假設 -}
      drop n (drop m xs)
 ===    {- |drop| 之定義 -}
      drop n (drop (Suc m) (x:xs)) {-"~~."-}
```
:::
:::

函數 |zip| 是另一個例子。我們可把 |zip xs ys| 視為 |xs| 之上的歸納定義：
```spec
zip :: List a -> List b -> List (a :* b)
zip []      ys      = []
zip (x:xs)  []      = []
zip (x:xs)  (y:yz)  = (x,y) : zip xs ys {-"~~."-}
```

:::{.exlist}
:::{.exer #ex:zipWith-map-uncurry-zip}
試定義 |zipWith :: (a -> b -> c) -> List a -> List b -> List c|,
並證明 |zipWith f xs ys = map (uncurry f) (zip xs ys)|.
:::
:::

## 完全歸納 {#sec:complete-induction}

說到遞迴定義，費氏數(Fibonacci number)
\index{Fibonacci number 費氏數}是最常見的教科書例子之一。
簡而言之，第零個費氏數是 |0|, 第一個費氏數是 |1|, 之後的每個費氏數是之前兩個的和。
寫成遞迴定義如下：
```spec
fib :: Nat -> Nat
fib 0      = 0
fib 1      = 1
fib (2+n)  = fib (1+n) + fib n {-"~~."-}
```
{.nobreak}但這和我們之前談到的歸納定義稍有不同。
我們已知定義 |f (Suc n)| 時可假設 |f| 在 |n| 之上已有定義。
但在 |fib| 的定義中，|fib (2+n)| 用到了 |fib| 的前*兩個*值。這樣的定義是可以的嗎？

函數 |fib| 的定義可以視為*完全歸納*\index{induction 歸納!complete induction 完全歸納}%
（又稱作*強歸納*）的例子。
回顧：先前介紹的數學歸納法中，使 |P n| 成立的前提之一是「對所有 |n|, 若 |P n| 成立， |P (Suc n)| 亦成立」。完全歸納則把這個前提增強如下：

> 給定述語|P :: Nat -> Bool|. 若
>
>   * 對所有小於 |n| 的值 |i|，|P i| 皆 成立，則 |P n| 亦成立，
>
> 則我們可得知 |P| 對所有自然數皆成立。

{.nobreak}以更形式化的方式可寫成：
```{.equation title="完全歸納：" #eq:complete-induction}
  |(forall n . P n) {-"~"-} <==  (forall n . P n  <== (forall i < n . P i)) {-"~~."-}|
```
{.nobreak}請注意：前提 |P n  <== (forall i < n . P i)| 隱含 |P 0| 成立，因為當 |n := 0|, 由於沒有自然數 |i| 滿足 |i < n|, 算式 |(forall i < n . P i)| 可化簡為 |True|.

在完全歸納法之中，證明 |P n| 時，我們可假設 |P| 對*所有*小於 |n| 的值都已成立了。
對寫程式的人來說，有了完全歸納法，表示我們日後定義自然數上的函數 |f :: Nat -> a| 時，每個 |f n| 都可以自由使用 |f| 在*所有*小於 |n| 的輸入之上的值。因此 |fib (2+n)| 可以用到 |fib (1+n)| 與 |fib n|, 因為 |n < 1+n < 2+n|.

:::{.example #eg:complete-induction-example}
關於完全歸納，離散數學教科書中的一個常見例子是「試證明所有自然數都可寫成不相同的二的乘冪的和」，例如 $50 = 2^5 + 2^4 + 2$.
這可用完全歸納證明。我們以半形式的方式論述如下：
令 |P n| 為「$n$可寫成一串不相同的二的乘冪的和」. 對所有 |n|, 我們想要證明 |P n  <== (forall i < n . P i)|. 當 |n| 為 |Zero|, 這一串數字即是空串列。
當 |n| 大於零，

  * 我們可找到最接近 |n| 但不超過 |n| 的二之乘冪，稱之為 |m|（也就是 $m = 2^k$ 而且 $m \leq n < 2\times m$）.
  * 由於 $n$ 不是 |Zero|, $m$ 也不是 |Zero|. 也因此 |n - m < n|.
  * 依據歸納假設 |(forall i < n . P i)|, 以及 |n - m < n|, |P (n-m)| 成立 --- |n - m| 可以寫成不相同的二的乘冪的和。
  * 也因此 |n| 可寫成不相同的二的乘冪的和 --- 把 |n-m| 加上 $m$ 即可.

上述證明僅用口語描述，因為如果形式化地寫下這個證明，就等同於寫個將自然數轉成一串二的乘冪的程式，並證明其正確性！下述函數 |binary| 做這樣的轉換，例如，|binary 50 = [32,16,2]|:
```haskell
binary :: Nat -> List Nat
binary Zero  = []
binary n     = m : binary (n -: m) {-"~~,"-}
   where  m     = last (takeWhile (<=n) twos)
          twos  = iterate (2 *:) 1 {-"~~."-}
```
{.nobreak}函數 |binary| 是一個完全歸納定義，和上述的證明對應得相當密切：串列 |twos| 是 |[1,2,4,8...]| 等等所有二的乘冪，|m| 是其中最接近而不超過 |n| 的。
遞迴呼叫 |binary (n -: m)| 是許可的，因為 |n - m < n|, 而根據完全歸納，我們已假設對所有 |i < n|, |binary i| 皆有定義。
:::

有了完全歸納法，我們在定義自然數上的函數時可允許更靈活的函數定義：
```spec
f :: Nat -> a
f b = ....                 {- 一些基底情況 -}
f n = ... f m ... f k ...  {- 如果 |m < n| 且 |k < n| -}
```
{.nobreak}|f n| 的右手邊可以出現不只一個遞迴呼叫，只要參數都小於 |n|.
但我們必須*確定上述定義中的幾個子句足以包含所有狀況，沒有狀況被遺漏*。
例如，我們若 把 |fib| 定義中的 |fib 1 = ...| 基底狀況去掉，
計算 |fib 2 = fib 1 + fib 0| 時便會出錯。

:::{.exlist}
:::{.exer #ex:sum-binary}
證明 |sum (binary n) = n|.
:::
:::{.exans}
使用完全歸納。

{.nobreak}**狀況** |n := Zero|: 等號兩邊都歸約為 |[]|.

{.nobreak}**狀況** |n > Zero|。
假設對於任何 |0 <= i < n|, |sum (binary i) = i|.
```spec
   sum (binary n) =
=    {- 令 |m = last (takeWhile (<=n) twos)|, |sum| 之定義 -}
   m +: sum (binary (n -: m))
=    {- 因 |n -: m < n|, 歸納假設 -}
   m +: (n -: m)
=  n {-"~~."-}
```
:::
:::{.exer #ex:fib-alpha}
證明當 |n >= 1|, |fib (2+n) > {-"\alpha^n"-}|, 其中
$\alpha = (1+\sqrt{5})/2$. 這個證明可用 |n := 1| 和 |n := 2| 當基底狀況。
:::
:::{.exans}
本證明的關鍵性質是 $\alpha^2 = (3+\sqrt{5})/2 = \alpha + 1$.
使用完全歸納證明 |fib (2+n) > {-"\alpha^n"-}|，以 |n := 1| 和 |n := 2| 當基底狀況。

{.nobreak}**狀況** |n := 1|: |fib 3 = 2 > {-"\alpha"-}|.

{.nobreak}**狀況** |n := 2|: |fib 4 = 3 > {-"(3+\sqrt{5})/2 = \alpha^2"-}|.

{.nobreak}**狀況** |n := 2+n| 且 |2+n > 4|。
假設對於任何 |3 <= i < 2+n|, |fib i > {-"\alpha^{i-2}"-}|. 論證：
```spec
    fib (2+n)
 =  fib (1+n) + fib n
 >    {- 歸納假設 -}
    {-"\alpha^{n-1}"-} + {-"\alpha^{n-2}"-}
 =    {- 提出 $\alpha^{n-2}$-}
    {-"(\alpha + 1) \times \alpha^{n-2}"-}
 =    {- $\alpha^2 = \alpha + 1$ -}
    {-"\alpha^2 \times \alpha^{n-2}"-}
 =  {-"\alpha^n"-} {-"~~."-}
```
:::
:::


{title="完全歸納 vs 簡單歸納"}
完全歸納有個較早的稱呼：*強歸納*(strong induction)。\index{induction 歸納!strong induction 強歸納}
原本的歸納法則相對被稱呼為*簡單歸納*或*弱歸納*。
強/弱歸納的稱呼可能使人以為完全歸納比簡單歸納更強 --- 意謂前者能證明出一些後者無法證明的定理。
事實上，完全歸納與簡單歸納是等價的：能用一個方法證出的定理，用另一個方法也能證出。
因此，使用哪一個純粹只是方便性的考量。

反應在程式設計上，給任一個完全歸納定義函數 |f :: Nat -> A|, 我們總能做出一個以簡單歸納定義的函數 |fs :: Nat -> List A|,
滿足 |fs n = map f [n, n-1, ... 0]|.
例如，函數 |fibs n| 傳回 |[fib n, fib (n-1).., fib 0]|.
```haskell
fibs :: Nat -> List Nat
fibs 0        = [0]
fibs 1        = [1,0]
fibs (Suc n)  = (x1+:x0) : x1 : x0 : xs  {-"~~,"-}
    where (x1:x0:xs) = fibs n {-"~~."-}
```
{.nobreak}由 |fib| 到 |fibs| 的轉換可能令讀者想起演算法中的*動態規劃*(*dynamic programming*)\index{dynamic programming 動態規劃}。我們將在日後談到這個話題。

{title="串列上的完全歸納"}
串列與自然數是類似的資料結構。串列上的完全歸納原則便是將 |Zero| 代換為 |[]|,
將 |Suc| 代換為 |(x:)|. 至於「小於」的關係，可定義為：
```spec
ys < xs  <=> ys `mem` tails xs && ys /= xs {-"~~."-}
```
{.nobreak}也就是說 |ys| 是 |xs| 的一個後段，但不是 |xs| 自己。
有了如上定義，串列上的完全歸納法是：
```{.equation title="串列的完全歸納："}
|(forall xs . P xs) {-"~"-} <==  (forall xs . P xs  <== (forall ys < xs . P ys)) {-"~~."-}|
```
{.nobreak}應用在編程上，當定義 |f (xs:)| 時，遞迴呼叫可作用在 |xs| 的任何後段上。

但對許多串列上的函數而言，這樣的模式還不夠靈活。我們得用下一節說到的良基歸納。

## 良基歸納 {#sec:well-founded-induction}

```texonly
%{
%format a0
%format a1
%format a2
%format an = "\Varid{a}_{\Varid{n}}"
```
*良基歸納*(*well-founded induction*)
\index{induction 歸納!well-founded induction 良基歸納}
可視為完全歸納的再推廣。
如果說完全歸納的主角是自然數，使用的是自然數上的「小於|(<)|」關係，良基歸納則將其推廣到任何型別，使用任一個*良基序*。
:::{.definition}
給定某型別 |A| 之上的二元關係 |(<:)|。如果從任意一個 |a0 :: A| 開始，均*不*存在無限多個滿足如下關係的 |a1|, |a2|\ldots :
```equation
   \ldots |<: a2 <: a1 <: a0| \mbox{~~,}
```
則 |(<:)| 可稱為一個*良基序*(*well-founded ordering*)\index{well-founded ordering 良基序}。
:::
把|b <: a| 簡稱為「|b| 小於 |a|」。
上述定義可以這麼地直覺理解：
給定任一個 |a0 :: A|，我們找一個滿足 |a1 <: a0| 的值 |a1|。
這種 |a1| 可能已不存在，但如果存在，我們再找一個滿足 |a2 <: a1| 的 |a2|.
說 |(<:)| 是個良基序的意思便是前述過程不可能永遠做下去：總有一天我們得停在一個「最小」的某*基底* |an :: A|。
```texonly
%}
```
舉例說明：自然數上的「小於|(<)|」關係是個良基序，但整數上的|(<)|關係則不是 --- 由於負數的存在。實數上的|(<)|關係也不是。良基序並非得是個全序(total order)。例如，我們可定義序對上的比較關係如下：
```spec
  (x1,y1) <: (x2,y2) {-"~"-}<=>{-"~"-} x1 < x2 && y1 < y2 {-"~~,"-}
```
{.nobreak}其中 |x1|, |y1|, |x2|, |y2| 都是自然數。
這麼一來，不論 |(1,4) <: (2,3)| 或 |(2,3) <: (1,4)| 都不成立，但 |(<:)| 仍是個良基序 --- 任何兩個自然數形成的序對不論以什麼方式遞減，最晚也得停在 |(0,0)|.

如果 |(<:)| 是個良基序，我們便可在其上做歸納。以直覺來理解的話，如果某函數定義成如此的形式（假設這幾個子句已經包括參數的所有可能情況）：
```spec
f :: A -> B
f b = ....                 {- 一些基底情況 -}
f x = ... f y ... f z ...  {- 如果 |y <: x| 且 |z <: x| -}
```
{.nobreak}由任何 |f x| 開始，若 |x| 不是基底情況之一，我們需遞迴呼叫 |f y| 和 |f z|。
但 |y| 和 |z| 在 |(<:)| 這個序上比 |x|「小」了一點。
此後即使再做遞迴呼叫，每次使用的參數又更小了一點。
而由於 |(<:)| 是良基序，|f| 的參數不可能永遠「小」下去 --- |f| 非得停在某個基底情況不可。
因此 |f| 必須正常終止。
同樣的原則也用在證明上：

> 給定述語|P :: A -> Bool| 以及 |A| 之上的良基序 |(<:)|。若
>
>   * 對所有滿足 |y <: x| 的值 |y|，|P y| 皆 成立，則 |P x| 亦成立，
>
> 則我們可得知 |P| 對所有 |A| 皆成立。

{.nobreak}或著可寫成如下形式：
```{.equation title="良基歸納："}
|(forall x . P x) {-"~"-} <==  (forall x . P x  <== (forall y <: x . P y)) {-"~~,\\"-}
{-"\qquad\mbox{其中 $(\lhd)$ 為一個良基序。}"-}|
```

{title="終止證明與良基歸納"}
我們已在許多地方強調：確定程式正常終止是很重要的。
我們也知道以簡單歸納與完全歸納定義出的程式均是會正常終止的。
但這兩種歸納定義的限制很多。雖然我們已舉了許多例子，仍有些程式難以套入它們所要求的模板中。
相較之下，良基歸納寬鬆許多。大部分我們已知、會終止的程式都可視為良基歸納定義。

或著，上述段落應該反過來說。
在函數程設中，欲證明某個遞迴定義的函數會終止，最常見的方式是證明該函數每次遞迴呼叫時使用的參數都在某個度量上「變小」了，而這個度量又不可能一直變小下去。
因此該函數遲早得碰到基底狀況。
換句話說，該函數每次遞迴呼叫的參數符合某個良基序；
*當我們如此證明一個函數會終止，其實就相當於在論證該函數是一個良基歸納定義*。
在指令式編程中證明某迴圈會終止的做法也類似。
最常見的方式是證明該迴圈每多執行一次，某個量值就會變小，而該量值是不可能一直變小的。
也就是說這些量值在每趟迴圈執行時的值符合某個良基序。

以下我們將看幾個遞迴定義的例子。請讀者們想想：這些函數總會正常終止嗎？為何？如果它們是良基歸納，使用的良基序是什麼？

:::{.example title="快速排序" #ex:quicksort}
以下是大家熟悉的*快速排序*(quicksort)
\index{quicksort 快速排序} [@Hoare:62:Quicksort]:
```spec
qsort :: List Int -> List Int
qsort []      = []
qsort (x:xs)  = qsort ys ++ [x] ++ qsort zs {-"~~,"-}
  where (ys,zs) = (filter (<=x) xs, filter (<x) xs) {-"~~."-}
```
{.nobreak}空串列是已經排序好的。當輸入為非空串列 |x:xs|，我們將 |xs| 分為小於等於 |x| 的，以及大於 |xs| 的，分別遞迴排序，再將結果接在一起。

函數 |qsort| 會正常終止，因為每次遞迴呼叫時，作為參數的串列都會減少至少一個元素（因為 |x| 被取出了），而串列的長度又不可能小於 |0|. 若要稍微形式地談這件事，可從良基歸納的觀點來看。如果定義：
```spec
ys <: xs {-"~"-}<=>{-"~"-} length ys < length xs {-"~~,"-}
```
{.nobreak}在 |qsort (x:xs)| 子句中，|ys <: xs| 和 |zs <: xs| 均被滿足，而 |(<:)| 是一個良基序。因此 |qsort| 是一個奠立在 |(<:)| 之上的良基歸納定義。
:::

:::{.example title="合併排序" #eg:mergesort}
在串列上，合併排序\index{merge sort 合併排序}也是很常使用的排序方式。
我們在第\@ref{sec:wholemeal}節中示範過以全麥編程方式寫成、由下往上的合併排序。
此處的寫法則更接近大家一般的認知：拿到一個長度為 |n| 的串列，將之分割為長度大致為 |n/2| 的兩段，分別排序之後合併。
同樣地，假設我們已有一個函數 |merge :: List Int -> List Int -> List Int|,
如果 |xs| 與 |ys| 已經排序好，|merge xs ys| 將它們合併為一個排序好的串列。
合併排序可寫成：
```spec
msort :: List Int -> List Int
msort []   = []
msort [x]  = [x]
msort xs   = merge (msort ys) (msort zs) {-"~~,"-}
  where (ys,zs) = (take (n `div` 2) xs, drop (n `div` 2) xs) {-"~~."-}
```
{.nobreak}要論證 |msort| 會正常終止，或著說，要將 |msort| 視為一個良基歸納定義，我們可用和例\@ref{ex:quicksort}中一樣的良基序|(<:)|.

但此處請讀者小心檢查：在 |msort xs| 子句中，|ys <: xs| 和 |zs <: xs| 有被滿足嗎？
當 |length xs = n|, 串列 |ys| 與 |zs| 的長度分別是 |n `div` 2| 和 |n - n `div` 2|. 當 |length xs = 1| 時，|ys| 與 |zs| 的長度分別是... |0| 和 |1| --- |zs| 並沒有變短！

這是為何我們需要 |msort [x]| 這個子句把 |length xs = 1| 的情況分開處理。如果沒有這個子句，|msort| 將有可能不終止 --- 讀者不妨試試看。
:::

:::{.example title="最大公因數" #eg:gcd}
歐幾里得(Euclid)的《幾何原本》成書於西元前三百年，其中描述「計算最大公因數」\index{greatest common divisor 最大公因數}的做法可能是世界上最古老的演算法。
以下函數計算兩個自然數 |(m,n)| 的最大公因數。
如果兩數相等，它們的最大公因數也是自身。
若兩數不相等，其最大公因數會是「大數減小數」與「小數」的最大公因數：
```haskell
gcd :: (Nat :* Nat) -> Nat
gcd (m,n)  | m == n     = n
           | otherwise  = gcd ((m `max` n) -: (m `min` n), m `min` n) {-"~~."-}
```
{.nobreak}這個程式總會正常終止嗎？為什麼？

事實上，若 |m| 或 |n| 其中之一為 |0|, |gcd (m,n)| 是不會終止的 ---
讀者不妨也試試看。
若 |m|, |n| 均為*正*整數呢？
首先我們先確立：如果初始的 |m|, |n| 均為正整數，|gcd| 每次遞迴呼叫拿到的參數也都是正整數 ---
確實如此，因為如果 |m > 0|, |n > 0|, 且 |m /= n|, 那麼 |(m `max` n) -: (m `min` n)| 與 |m `min` n| 都不會是零或負數。
接下來我們可論證：如果 |m|, |n| 均為正整數，每次遞迴呼叫中，*兩參數的和*都變小了一些。確實：
```spec
   (m `max` n) -: (m `min` n) +: (m `min` n)
=  m `max` n
<   {- |m|, |n| 均為正整數 -}
   m + n {-"~~."-}
```
{.nobreak}因此，我們可得知 |gcd| 在 |m|, |n| 均為正整數時會正常終止。
如果把 |gcd| 當作一個良基歸納，我們用了如下的良基序：
```texonly
%{
%format m1
%format n1
%format m2
%format n2
```
```spec
  (m1, n1) <: (m2, n2) {-"~"-}<=>{-"~"-}  m1+n1 < m2+n2 {-"~~,"-}
```
{.nobreak}其中 |m1|, |n1|, |m2|, |n2| 均為正整數。
```texonly
%}
```
:::

:::{.example title="Curried 函數" #ex:interleave}
下述函數 |interleave| 將兩個參數中的元素交錯放置。
例如 |interleave [1,2,3] [4,5] = [1,4,2,5,3]|.
```haskell
interleave :: List a -> List a -> List a
interleave []      ys  = ys
interleave xs      []  = xs
interleave (x:xs)  ys  = x : interleave ys xs {-"~~."-}
```
{.nobreak}這可視為一個良基歸納定義嗎？
若將 |interleave| 做為傳回函數的高階函數看待，我們比較難看出它是定義在什麼良基序上的。
但若把 |interleave| 的兩個參數一起考慮，我們不難看出什麼度量在遞迴呼叫後「變小」了：兩個參數長度的和！

凡是遇到像 |interleave| 的 curried 函數，我們也可考慮它的 uncurried 版本：
```haskell
interleave' :: (List a :* List a)-> List a
interleave' ([],    ys)  = ys
interleave' (xs,    [])  = xs
interleave' (x:xs,  ys)  = x : interleave' (ys,xs) {-"~~."-}
```
{.nobreak}函數 |interleave'| 是個良基定義 --- 參數中的兩個串列雖然交換位置，但它們長度的總和會變小。也就是說 |interleave'| 可視為定義在這個良基序上的函數：
```texonly
%{
%format xs1
%format xs2
%format ys1
%format ys2
```
```spec
  (xs1,ys1) <: (xs2,ys2) {-"~"-}<=>{-"~"-} length xs1 + length ys1 < length xs2 + length ys2 {-"~~."-}
```
```texonly
%}
```
凡是 |interleave'| 有的性質，不難找出 |interleave| 的相對應版本；
證明 |interleave| 的性質時，可當成是在證明 |interleave'| 的相對性質。
因此我們也會比較寬鬆地說 |interleave| 也是 |(<:)| 之上的良基歸納定義。
:::

:::{.example #eg:McCarthy91}
下列函數被稱作「McCarthy 91 函數」：
```haskell
mc91 :: Nat -> Nat
mc91 n  | n > 100    = n -: 10
        | otherwise  = mc91 (mc91 (n +: 11)) {-"~~."-}
```
{.nobreak}讀者不妨先猜猜看 |mc91| 會傳回什麼？答案是，|mc| 和以下函數是等價的：
```spec
mc91'  | n > 100    = n -: 10
       | otherwise  = 91 {-"~~."-}
```
\todo{finish this.}
:::

## 詞典序歸納 {#sec:lexicographic-induction}

\index{induction 歸納!lexicographic induction 詞典序歸納}
我們終於要定義第\@ref{sec:wholemeal}節與\@ref{sec:well-founded-induction}節中都提到的「合併」函數：將兩個已排序好的串列合而為一。
函數 |merge| 最自然的寫法可能是：
```spec
merge :: List Int -> List Int -> List Int
merge []      ys      = ys
merge (x:xs)  []      = x:xs
merge (x:xs)  (y:ys)  = if x <= y  then x : merge xs (y:ys)
                                   else y : merge (x:xs) ys {-"~~."-}
```
{.nobreak}如果兩個串列之中有一個為空串列，合併的結果是另一個。
如果兩個都不是空串列，我們比較其第一個元素，以便決定將哪個當作合併後的第一個元素。

但，|merge| 最後一個子句的第一個遞迴呼叫中，|y:ys| 沒有變短；第二個遞迴呼叫中，|x:xs| 沒有變短。
這種程式會終止嗎？如果會，是哪種歸納定義呢？

一種看法是將 |merge| 視作和例\@ref{ex:interleave}中的 |interleave| 類似的歸納定義：兩個參數的長度和在遞迴呼叫中變小了。另一個可能是將函數 |merge| 視作*詞典序歸納*(*lexicographic induction*)的例子 --- 詞典序歸納也是良基歸納的一個特例。

先介紹*詞典序*。我們怎麼決定兩個英文單字在詞典中的先後順序呢？
通常是先比較其第一個字母，如果第一個字母便分出了大小，就以此大小為準，*不論剩下的字母為何*。如果第一個字母一樣，便從第二個字母開始比起。
若要以形式化的方式寫下詞典序的定義，我們考慮一個較簡單的狀況：如何比較 |x1 y1| 和 |x2 y2| 兩個長度均為二的字串？如果 |(<)| 是比較單一字元大小的順序，我們把兩個字元的詞典序寫成 $(<;<)$，定義如下：
```equation
    x_1 y_1 (<;<) x_2 y_2 ~~\equiv~~
       x_1 < x_2 ~\vee~ (x_1 = x_2 \wedge y_1 < y_2)  \mbox{~~.}
```
{.nobreak}如前所述，先比較 |x1| 與 |x2|, 如果相等，再比較 |y1| 與 |y2|.

我們可以再稍微擴充一些，考慮 $x_i$ 與 $y_i$ 型別不同的情況：
:::{.definition #def:lhd-prec}
給定義在型別 |A| 之上的序 $(\lhd)$ 和型別 |B| 之上的序 $(\prec)$, 它們的*詞典序*(*lexicographic ordering*)，寫做 $(\lhd;\prec)$，是 |(A :* B)| 上的一個序，定義為：
```equation
    (x_1, y_1) (\lhd;\prec) (x_2,y_2) ~~\equiv~~
       x_1 \lhd x_2 ~\vee~ (x_1 = x_2 \wedge y_1 \prec y_2)  \mbox{~~.}
```
:::
{.nobreak}上述定義也可擴充到三個、四個... 元素的序對上。此處便不把他們寫出來了。

關於詞典序的有趣性質相當多，此處僅用到下述性質
:::{.theorem #thm:lhd-prec}
如果 $(\lhd)$ 與 $(\prec)$ 均為良基序，$(\lhd;\prec)$ 也是良基序。
:::
{.nobreak}因此，$(\lhd;\prec)$ 也可用來做歸納定義。
我們把使用詞典序的良基序歸納稱作「詞典序歸納」。

回頭看 |merge| 的定義。先考慮下述、在第\@ref{sec:wholemeal}節中出現的 uncurried 版本：
```spec
merge' :: (List Int :* List Int) -> List Int
merge' ([],    ys)    = ys
merge' (x:xs,  [])    = x:xs
merge' (x:xs,  y:ys)  = if x <= y  then  x : merge' (xs, y:ys)
                                   else  y : merge' (x:xs, ys) {-"~~."-}
```
{.nobreak}如果 |(<:)| 是比較串列長度的良基序，我們可說 |merge'| 是在 $(\lhd;\lhd)$ 之上的歸納定義。確實，

  * |(xs, y:ys) (<:;<:) (x:xs,  y:ys)|, 因為 |xs <: x:xs|;
  * |(x:xs, ys) (<:;<:) (x:xs,  y:ys)|, 因為 |x:xs = x:xs| 且 |ys <: y:ys|.

{.nobreak}至於 |merge| 則是 |merge'| 的 curried 版本，因此也是定義良好的。

如前所述，函數 |merge| 的定義不一定得看成辭典序歸納 --- 它也可和 |interleave| 一樣看成另一種較簡單的良基歸納 --- 比較兩參數的長度之和。
接下來的例子就得倚靠辭典序歸納了。

:::{.example #eg:Ackermann-function}
知名的 Ackermann 函數 (Ackermann's function)
\index{Ackermann's function Ackermann 函數}
是一個遞增得相當快的函數。
```haskell
ack :: Nat -> Nat -> Nat
ack 0        n        = Suc n
ack (Suc m)  0        = ack m 1
ack (Suc m)  (Suc n)  = ack m (ack (Suc m) n) {-"~~."-}
```
{.nobreak}該函數定義上的特殊處之一是 |ack (Suc m) n| 的結果又被當作 |ack m| 的參數，因此較難以用理解 |interleave| 的方式理解。
但它可以視為詞典序 |(<;<)| 上的歸納：

  * |(m,1) (<;<) (Suc m,0)|，因為 |m < Suc m|;
  * |(Suc m, n) (<;<) (Suc m, Suc n)|，因為 |n < Suc n|;
  * |(m, ack (Suc m) n) (<;<) (Suc m, Suc n)|，因為 |m < Suc m|.


:::

## 交互歸納 {#sec:mutual-induction}

許多工作無法由一個函數獨立完成，而需要許多函數彼此呼叫。本章最後談談這類的*交互歸納*(mutual induction)定義。\index{induction 歸納!mutual 交互}
下列函數定義中，|even| 判斷其輸入是否為偶數。第二個子句告訴我們：如果 |n| 是奇數， |Suc n| 便是偶數。但如何判斷一個數字是否為奇數？如果 |n| 是偶數，|Suc n| 便是奇數：
::: {.multicols}
::: {.mcol width="0.5\\textwidth"}
```spec
even :: Nat -> Bool
even Zero     = True
even (Suc n)  = odd n  {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```spec
odd :: Nat -> Bool
odd Zero     = False
odd (Suc n)  = even n {-"~~."-}
```
:::
:::

這類彼此呼叫的定義可以視為一整個大定義。
為讓讀者習慣，我們先把 |even| 與 |odd| 的定義改寫為 $\lambda$ 算式與 |case|:
::: {.multicols}
::: {.mcol width="0.5\\textwidth"}
```spec
even = \n ->  case n of
                Zero   -> True
                Suc n  -> odd n  {-"~~,"-}
```
:::
::: {.mcol width="0.5\\textwidth"}
```spec
odd = \n ->  case n of
               Zero   -> False
               Suc n  -> even n {-"~~."-}
```
:::
:::
{.nobreak}上述的定義可以合併成一個：|evenOdd| 是一個序對，其中有兩個函數 |Nat -> Bool|，其中是 |fst evenOdd| 就是 |even|，|snd evenOdd| 就是 |odd|:
```haskell
evenOdd :: ((Nat -> Bool) :* (Nat -> Bool))
evenOdd = (  \n -> case n of{-"~~"-}  Zero   -> True
                                      Suc n  -> snd evenOdd n,
             \n -> case n of{-"~~"-}  Zero   -> False
                                      Suc n  -> fst evenOdd n) {-"~~."-}
```

:::{.exlist}
:::{.exer #ex:zip-inits-tails}
證明 |all (xs ==) (zipWith (++) (inits xs) (tails xs))|. (unfinished)
:::
:::{.exans}
在 |xs| 上做歸納。
```spec
    all ((x:xs) ==) (zipWith (++) (inits (x:xs)) (tails (x:xs)))
<=> all ((x:xs) ==) (zipWith (++) ([]: map (x:) (inits xs)) ((x:xs):tails xs))
<=> all ((x:xs) ==) (([] ++ (x:xs)) : zipWith (++) (map (x:) (inits xs)) (tails xs))
<=> ((x:xs) == (x:xs)) &&
    all ((x:xs) ==) (zipWith (++) (map (x:) (inits xs)) (tails xs))
```
:::
:::

## 參考資料 {#sec:induction-ref}

快速排序\index{quicksort 快速排序}最初由 Hoare 在 Communications of the ACM 的演算法專欄中發表為兩個獨立的演算法：
將陣列分割為大、小兩塊的「演算法63: PARTITION」[@Hoare:61:Partition]，
以及用前述演算法將陣列排序的「演算法64: QUICKSORT」[@Hoare:61:Quicksort]。
至於「演算法65: FIND」[@Hoare:61:Find] 的功能則是：給定 |k|，尋找一個陣列中第 |k| 小的元素。
該演算法也使用了 PARTITION, 我們現在常把它稱為「快速選擇(quickselect)」\index{quickselect 快速選擇}。
該專欄要求作者使用 Algol 語言。Algol 支援遞迴，Hoare 也大方地用了遞迴。
當時遞迴仍是新觀念，Hoare 在另一篇論文[@Hoare:62:Quicksort]中（以大量文字）描述不用遞迴的作法。

例\@ref{ex:quicksort}中的快速排序常被當作「函數編程（或 Haskell）漂亮又簡潔」的例證：快速排序用其他語言得寫得落落長，用 Haskell 可在兩三行內清楚地寫完。
但這樣的比較並不很公平：例\@ref{ex:quicksort}排序的是串列，而拿來比較的對象通常是將陣列做排序的指令式語言程式。
快速排序的主要挑戰之一，也是「演算法63: PARTITION」的重點，是在$O(n)$的時間、$O(1)$的額外空間之內完成陣列的分塊。
這點在串列版本中並沒有（或不須）表達出來。

@MannaMcCarthy:69:Properties
@MannaPnueli:70:Formalization
