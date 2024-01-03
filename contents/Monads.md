``` {.haskell .invisible}
{-# LANGUAGE TypeOperators #-}
module Chapters.Monads where

import Prelude ()
import Control.Arrow ((***))
import Common.MiniPrelude hiding (exp, length, take, drop, gcd)
import Chapters.Basics (ETree(..), ITree(..))
```

# 單子與副作用 {#ch:monads}

從純函數語言的觀點而言，程式是函數，而函數的「本分」是把一個輸入值對應到一個輸出值，除此之外發生的都是*副作用*(side effects)\index{side effect 副作用}。
一個程式執行時若可能改變某個*可變變數*(*mutable variable*)的值，是一種副作用 --- 這可能是大家最耳熟能詳的例子。^[在數學式或函數語言程式中，例如 |x + 2*y + 1|, 其中的 |x| 和 |y| 被稱為 ``variables''，譯為「變數」。這名稱的由來是：相對於 |1|, |2| 等等常數，「變數」的值被其所屬環境而決定。但在同一個環境與範圍(scope)中，一個變數仍代表同一個值。
命令式語言中的「變數」則是存放值的容器，我們可使用賦值(assignment)指令改變變數中的值。為了區分，我們把後者這種能被賦值而改變內容的變數稱作「可變變數(mutable variables)」。]
此外，讀寫檔案、抓滑鼠的位置、往螢幕寫東西、和系統問現在的日期時間、取亂數等等，也是副作用。
程式若拋出例外(exception)、不傳回值了，是一種副作用。
一個程式若有不止一個可能的傳回值（程式員無法預測是哪一個），也是一種副作用。
在更嚴格的定義中，一個程式如果進入無窮迴圈而不終止（因此不傳回值），也可視為副作用。

許多程式設計典範都大量依靠副作用完成各種工作：更新變數、輸出入、用例外處理執行時間遇到的錯誤...。
在大家的一般印象中，純函數語言反其道而行，其特徵就是「不能有副作用」。
但這其實是個過度簡化的說法。
實情正好相反：純函數語言不僅允許副作用，甚至允許多種副作用並存，並且可把一個程式所被允許的副作用標示在其型別中。
只是，副作用也必須被納入嚴謹的數學架構中。
在純函數語言中，我們需好好地談每個副作用到底「是什麼」（即其語意為何），滿足哪些性質，而這些性質便可用來推論含副作用的程式的正確性。

例如，「拋出例外(exception)」\index{side effect 副作用!exception 例外}算是一種副作用。
如果我們定義如下的型別：
```spec
data Except b = Exception String | Return b {-"~~,"-}

```
{.nobreak}那麼一個正常終止時傳回型別為 |b| 的值、但也有可能拋一個例外（並附帶一個字串錯誤訊息）的程式可視為一個值域為 |Except b| 的全函數 --- 正常終止時傳回 |Return x|, 「拋出例外」則可用傳回 |Exception msg| 來模擬。
有多個可能傳回值（型別均為|b|）的程式可視為值域為 |Set b| 的全函數 --- 所有可能的回傳值都被收集在集合之中。
假設有一個型別為 |s| 的可變變數，那麼一個執行完畢後會傳回 |b|、但可能改變該可變變數的程式可以視為一個型別為 |s -> (b, s)| 的函數 --- 輸入的 |s| 為該可變變數的初始值，輸出的序對中，|b| 是程式的結果，|s| 是可變變數的新值。例如，當 |s| 為 |Int|, 一個傳回該可變變數的現有值、並同時將變數加一的「指令」可表示成一個函數 |\s -> (s, 1+s)|.

如此一來，我們可在純函數語言中實作出許多種副作用。
這可能和讀者心目中的「實作」相當不同 ---
此處的「將可變變數加一」並沒有真正去修改原記憶體位置中的值，而是產生了一個新值；
「拋例外」並未採用高效率的實作（例如到系統堆疊中把回傳位置一個個 pop 出來），而和一般函數一樣，只是傳回一個資料結構。
但我們可把前述這些較有效率的做法當作交給編譯器做的最佳化 --- 當編譯器看到傳回 |Except b| 的函數，或著看到 |s -> (b, s)| 這樣的函數，可自己想辦法去找有效率的編譯方式。^[實務上這相當不容易...TODO]
身為程式員，我們在乎的是將「會拋例外的程式其實是什麼？會修改可變變數的程式其實是什麼？」給描述出來。

另一個可能令讀者困擾的是：這樣寫程式實在不方便。一個使用 |Except| 的程式可能得有許多 |case| 將子程式的結果配對拆開。一個程式若由許多型別為 |s -> (b, s)| 的組成，得手動將序對配對，將輸入與輸出的 |s| 傳來傳去。
這些做法都太低階，我們希望能在抽象一點的層次上工作，方便我們寫程式、讓我們能做抽象些的思考。
這個抽象概念必須能適用於種種副作用，抓出這些副作用的共同模式。

在 Haskell 中，描述副作用最常用的抽象概念是*單子*(*monad*)。\index{monad 單子}
大家常認為單子是學習函數語言碰上的第一個難關。
希望讀者讀完本章後，會發現它其實沒那麼難。
一般談單子的方式是由下往上的：由例外、可變變數等等特例的實作開始，歸納出這些特例的共同模式，使讀者可發現引出單子這個概念的動機。
從第 \@ref{sec:exceptions} 節開始，我們也將由這種觀點出發解說單子。
但也有另一種由上而下的看法：先討論單子與每個副作用的運算子該滿足什麼性質，才談他們可怎麼實作。我們認為這種看法一樣重要。

{title="例：簡單算式求值"}
以下的資料結構 |Expr| 表達一個只有整數、負號、和加法的數學式：

```spec
data Expr = Num Int | Neg Expr | Add Expr Expr {-"~~."-}
```
{.nobreak}例如 |-3 + 4| 可表達為 |Add (Neg (Num 3)) (Num 4)|.
我們可輕易寫一個歸納定義，將一個 |Expr| 計算成一個整數：
```spec
eval :: Expr -> Int
eval (Num n)      = nw
eval (Neg e)      = - (eval e)
eval (Add e0 e1)  = eval e0 + eval e1 {-"~~."-}
```

看來這是個再單純也不過的純函數。但只要我們稍加擴充這個數學式型別，情況就變複雜了。
如果數學式有除法，分母為零時 |eval| 就得拋出例外；
我們可以為數學式加入變數，那麼 |eval| 碰到變數時得查閱該變數的值；
我們也許想要用一個可變變數幫我們記住 |eval| 做了多少次加法。
程式只要稍微變複雜，我們就會開始需要許多種副作用。

我們將用這個例子介紹單子。在接下來的幾個章節中，我們將以不同的方式擴充 |Expr| 型別以及 |eval| 函。
每個擴充需要不同的副作用。
我們將由如何模擬出副作用為動機出發，介紹單子的概念。
引入單子這種抽象化後，我們會發現我們只需改用不同的單子，就可以在不太改變 |eval| 的主要程式的情況下，為 |eval| 加入新的副作用。
因此單子可以視為模組化地加入副作用的方法

## 例外處理 {#sec:exceptions}
\index{side effect 副作用!exception 例外}

假設我們添了一個整數除法運算元：
```spec
data Expr = Num Int | Neg Expr | Add Expr Expr | Div Expr Expr  {-"~~,"-}
```
{.nobreak}我們便碰到了一個小難題：要怎麼處理分母是零的狀況呢？

Haskell 的 |div| 函數可做整數除法。碰到分母為零時，|div| 和大部分語言的除法函數一樣讓整個程式當掉。我們不希望程式當掉，因此得在呼叫 |div| 前先檢查一下分母是否為零。但當分母真為零，|eval| 應該傳回什麼呢？
```spec
eval (Div e0 e1) =  let v1 = eval e1
                    in if v1 /= 0 then eval e0 `div` v1 else ???
```

{title="用 |Maybe| 表達部份函數"}
一種看法是，有了除法後，|eval| 對於某些輸入沒有對應的值，因此 |eval| 成了一個部份 (partial) 函數。\index{function 函數!partial 部分函數}

操作上，我們希望 Haskell 提供拋出例外的功能，|eval| 無值可傳的時候便拋出例外。在程式的另外某處可能接住這些例外，另行處理。
本章開頭提及，一個傳回 |Int|、但可能拋出例外的函數可用傳回 |Except Int| 的全函數來模擬。|Except| 再給一次如下：
```spec
data Except b = Expt String | Return b {-"~~."-}

```
我們把 |eval| 的型別改為 |Expr -> Except Int|, 正常運算結束便傳回 |Return|, 碰到分母為零的情形則傳回 |Expt|.

這個版本的 |eval| 該怎麼寫呢？碰到 |Num n| 自然是傳回 |Return n|:
```spec
eval (Num n) = Return n {-"~~."-}
```
{.nobreak}處理 |Neg e| 的條款則比以前稍微複雜了。我們得檢查 |eval e| 的結果，若是 |Return v|，應傳回 |-v|，但也需包上一個 |Return|. 如果遇到 |Expt msg|, 表示 |e| 的運算失敗了，我們只好把 |Expt msg| 再往上傳。
```spec
eval (Neg e) =  case eval e of
                  Return v  -> Return (-v)
                  Expt msg  -> Expt msg  {-"~~."-}
```
{.nobreak}|Add| 的情況下，程式碼看來更冗長了些：
```spec
eval (Add e0 e1) =  case eval e0 of
                     Return v0  ->  case eval e1 of
                                      Return v1  -> Return (v0 + v1)
                                      Expt msg   -> Expt msg
                     Expt msg   ->  Expt msg  {-"~~."-}
```
{.nobreak}我們得分別檢查 |eval e0| 與 |eval e1| 的結果是 |Return| 或是 |Expt|，因此用兩層 |case| 分出了四個狀況 --- 雖然它們是重複性很高的程式碼。
最後是 |Div e0 e1| 的情況，我們先計算 |e1|, 如果是零的話傳回 |Expt|, 含錯誤訊息 |"division by zero"|, 否則做除法運算。
在這過程中我們也需要許多 |case| ：
```spec
eval (Div e0 e1) =  case eval e1 of
                     Return 0   ->  Expt "division by zero"
                     Return v1  ->  case eval e0 of
                                      Return v0  -> Return (v0 `div` v1)
                                      Expt msg   -> Expt msg
                     Expt msg   ->  Expt msg  {-"~~."-}
```
{.nobreak}很自然地，我們會希望把這些例行公事抽象掉。

{title="|Except| 作為單子"}
再看一次處理 |Neg| 的條款：
```spec
eval (Neg e) =  case eval e of
                  Return v  -> Return (-v)
                  Expt msg  -> Expt msg {-"~~."-}
```
{.nobreak}我們真正想表達的僅是「把 |eval e| 的結果送給 |\v -> Return (-v)| --- 如果有結果的話」。這只是多加了一點手續的函數應用 (application)。回想 Haskell 有個函數應用運算元|($) :: (a -> b) -> a -> b|.
給定 |f :: a -> b| 和 |x :: a|, 那麼 |f $ x| 就是把 |x| 餵給 |f|（也就是 |f x|）。
也許我們可以自己定義一個函數應用運算元 |(=<<)|. 概念上，|f =<< x| 仍是把 |x| 餵給 |f|，但 |x| 的型別是 |Except a|, |f| 的型別是 |a -> Except b|, 而「檢查 |x| 是 |Return| 或 |Expt|」的動作就可藏在 |(=<<)| 之中（讀者可把 |(=<<)| 的型別和 |($)| 做比較）：
```spec
(=<<) :: (a -> Except b) -> Except a -> Except b
f =<< Return x  = f x
f =<< Expt msg  = Expt msg {-"~~."-}
```
{.nobreak}如此一來，|eval (Neg e)| 的條款可簡潔地寫成：
```spec
eval (Neg e) = (\v -> Return (-v)) =<< eval e  {-"~~,"-}

```
{.nobreak} 如果定義 |negate x = -x|, 上式的右手邊可以更簡潔地寫成 |Return . negate =<< eval e|.

但，目前較常見的習慣是把這個運算子的左右顛倒：參數寫前面，函數寫後面。也就是定義:
```spec
(>>=) : Except a -> (a -> Except b) -> Except b
Just x   >>= f = f x
Nothing  >>= f = Nothing {-"~~."-}
```
{.nobreak}運算子 |(>>=)| 唸作 ``bind'', 是我們將會細談的重要元素。
有了它，函數 |eval| 的前兩個條款可以改寫如下：
```spec
eval (Num n)  = return n
eval (Neg e)  = eval e >>= \v -> return (-v) {-"~~."-}
```
{.nobreak}我們把 |Return| 寫成函數：|return = Return|。等下會解釋為什麼。
注意：依照 Haskell 的運算元優先順序，
|m >>= \v -> e| 會被理解成 |m >>= (\v -> e)|.
|Add| 和 |Div| 的情況也可以用 |(>>=)| 改寫:
```spec
eval (Add e0 e1) =  eval e0  >>= \v0 ->
                    eval e1  >>= \v1 ->
                    return (v0 + v1)
eval (Div e0 e1) =  eval e1  >>= \v1 ->
                    if v1 == 0 then throw "division by zero"
                    else  eval e0 >>= \v0 ->
                          return (v0 `div` v1) {-"~~."-}
```
{.nobreak}此處我們把 |Expt| 寫成 |throw|.

如此一來，我們的程式變得簡短了一些。例如，|eval (Add e0 e1)| 直覺上彷彿在說「把 |eval e0| 的結果叫做 |v0|, |eval e1| 的結果叫做 |v1|, 然後傳回 |v0 + v1|」，至於判斷 |eval e0| 與 |eval v1| 到底是 |Return| 還是 |Expt| 的動作則藏在 |(>>=)| 之中了。
但引入 |(>>=)| 這個抽象的用意並不只是把程式變短，而是可推廣到其他的副作用之上。這將是接下來幾小節的主題。

提醒一下：
有些讀者可能認為 |eval| 的後兩個條款看來像命令式語言：|eval e1 >>= \v1 -> ..| 看來就像是 |v1 := eval e1| --- 把 |eval e1| 的值寫到 |v1| 中。
但其實 |(>>=)| 並沒有賦值（改變變數現有的值）之意，要做比較的話，它更像是增強版的 |let|.
算式 |p >>= \x -> e| 就像是 |let x = p in e|.
兩者都是「把 |p| 的值算出，給予一個名字 |x|, 然後計算 |e|」。
差別則是：

  * |let| 處理純的值：在 |let x = p in e| 之中，如果 |p| 的型別是 |a|, |x| 的型別也是 |a|; 算式 |e| 的型別若是 |b|, 整個式子的型別也是 |b|;  |e| 的型別相同。
  * |(>>=)| 處理含有 |Except| 的值：在 |p >>= \x -> e| 之中，
    * |p| 的型別得有 |Except|. 如果 |p| 的型別是 |Except a|, 則 |x| 的型別是 |a|;
    * |e| 的型別得有 |Except|. 如果 |e| 的型別是 |Except b|, 整個式子的型別也是 |Except b|.
    * 因此 |\x -> e| 是一個型別為 |a -> Except b| 的函數。

{title="捕捉例外"}
最後，我們可以定義一個捕捉例外的運算子。算式 |catch p hdl| 嘗試配對 |p| 的值，
如果是 |Return x|, 就傳回結果 |x|；如果是 |Expt msg|, 就把錯誤訊息 |msg| 交給例外處理函數 |hdl|。
當 |p| 的型別是 |Except a|, |catch p hdl| 的型別也是 |a|, 而 |hdl| 的型別必須是 |String -> a|:
```spec
catch :: Except a -> (String -> a) -> a
catch (Return x)  hdl = x
catch (Expt msg)  hdl = hdl msg {-"~~."-}
```

例如，下式嘗試計算 |e| 並把結果轉成字串。如果 |e| 能正常計算，字串會是 |"Result:"| 開頭，否則是 |"Error:"| 開頭：
```spec
   catch (eval e)  (\v -> "Result: " ++ show v)
                   (\msg -> "Error: " ++ msg)  {-"~~."-}
```
{.nobreak}下式則無論如何都傳回 |Int|, 如果 |e| 之中出現了分母為零的除法，我們便傳回 |65536|:
```spec
   catch (eval e) id (const 65536) {-"~~."-}
```

## 單子與單子律 {#sec:monad-class-laws}

第 \@ref{ch:intro} 章提及，「抽象化」意指抽取出一個問題中最關鍵的元素。
一個成功的抽象化能抓到同類問題的共通本質，因此可以推廣到其他相關的情境、問題，用同一套方法表達這些情境、解決這些問題。
我們在第 \@ref{sec:exceptions} 節發現的便是一個關於計算與副作用的成功抽象化。

我們可以把第 \@ref{sec:exceptions} 節中的 |Except a| 理解成一個 *尚待完成的計算*，或是一個*尚待執行的程式*。
用 |case| 去配對它便是把這個計算算出來、把程式執行出來。
如果順利執行，計算結果的型別為 |a|, 但也可能產生副作用。
而由其型別建構子 |Except| 可看出此處可能的副作用是「可能拋出例外」。
運算子 |(>>=)| 的功用是將小計算/程式串接起來，組成較大的計算/程式。

推廣出去，|Except| 其實可以是任意一個型別建構元 |m|: 一個型別為 |m a| 的值表示一個尚待完成的計算，或是一個尚待執行的程式。如果順利執行，計算結果的型別為 |a|, 但執行過程中可能產生副作用。
至於究竟是什麼副作用，則看 |m| 是什麼而定。
此外，每個 |m| 附帶兩個運算子：
  * |return :: a -> m a|;
  * |(>>=) :: m a -> (a -> m b) -> m b|.

{.nobreak}它們三者合稱為一個*單子*(*monad*).\index{monad 單子}

給任一個值 |x :: a|, 運算子 |return x| 代表一個純粹傳回 |x|, 沒有副作用的計算。以 |m = Except| 為例，自然的選擇是令 |return = Return|. 我們之後會看到其他例子。

運算子 |(>>=)| 將小計算串接在一起。
在 |p >>= f| 之中，|p :: m a| 是一個回傳型別將為 |a|, 但可能有副作用的計算。
如果 |p| 被算出來，其結果會被傳給 |f|.
函數 |f :: a -> m b| 是一個拿到 |p| 的結果後*算出一個計算的計算*.
整個式子 |p >>= f| 的型別也是 |m b|.
這是理解單子程式的一個重點：函數本身沒有副作用，但*函數可以算出含有副作用的程式*。
如果我們把 |f| 寫成 $\lambda$ 表示式，
在 |p >>= \x -> e| 之中，|p| 的結果被取名為 |x|，而 |e :: m b| 之中可以使用 |x|.
此處 |(>>=)| 可理解成由兩個小計算 |p| 與 |e| 組出一個大計算的接著劑，兩個小計算用 |x| 來溝通。

運算子 |return| 與 |(>>=)| 是用來組合出含有副作用的程式的元件，因此得滿足一些該有的性質。正式說來，
:::{.definition title="單子" #def:monad}
一個單子(monad)\index{monad 單子}包含一個型別建構子 |m|,
以及兩個運算子 |return :: a -> m a| 與 |(>>=) :: m a -> (a -> m b) -> m b|. 它們須滿足以下三條*單子律*：\index{monad laws 單子律}

:::{.equations}
  * {title="右單位律(right identity): " #eq:monad-right-id}
    |p >>= return {-"~"-}| |={-"~"-} p {-"~~,"-}|
  * {title="左單位律(left identity): " #eq:monad-left-id}
    |return x >>= f {-"~"-}| |={-"~"-} f x {-"~~,"-}|
  * {title="結合律(associativity): " #eq:monad-assoc}
    |(p >>= f) >>= g {-"~"-}| |={-"~"-} p >>= (\x -> f x >>= g) {-"~~."-}|



:::

:::

*右單位律*若寫成 |p >>= \x -> return x| 也許更好理解。計算 |p| 的結果 |x| 被傳到 |(>>=)| 的右邊，但後者只是單純地把 |x| 再傳出。這和只寫 |p| 得是一樣的。

在*左單位律*的左手邊 |return x >>= f| 之中，函數 |f| 接收 |return x| 的結果 --- 而 |return x| 的結果就是 |x|! 因此這和 |f x| 得是一樣的。

最後一條是 |(>>=)| 的*結合律*：「用 |p| 與 |f| 串接出一個程式，再把 |g| 串接到右邊」與「把 |f| 與 |g| 串接在一起，並把 |p| 串接在它們左邊」得到的必須是一樣的程式。
但由於型別的問題，在後者的情況我們需要一個 |x| 表示 |p| 的結果，前者則不用。

每定義一個新的單子，我們需選定一個型別 |m|，定義 |return| 與 |(>>=)| 兩個運算子，然後證明它們滿足單子律。需要推論含單子的程式的性質與正確性時，這三條單子律也是我們會用到的性質。

最後一提：定義 \@ref{def:monad} 並不是單子的唯一定義方式。其他等價的定義詳見 \todo{where}.

:::{.exlist}
:::{.exer}
證明第 \@ref{sec:exceptions} 節中的定義滿足單子律。
意即當 |m = Except|, |return = Return|, 而 |(>>=)| 的定義如第 \@ref{sec:exceptions} 節所示時，三條單子律都成立。
:::
:::

{title="單子 class"}
既然 Haskell 有 type class 機制，我們可以把單子定義為一個 class:
```spec
class Monad m where
  return  :: a -> m a
  (>>=)   :: m a -> (a -> m b) -> m b {-"~~."-}
```
如此明確規定一個屬於 |Monad| 的型別建構子必須有 |return| 與 |(>>=)|.
|Except| 型別則是其中的一個特例：
```spec
instance Monad Except where
   return           = Return
   Expt msg  >>= f  = Expt msg
   Return x  >>= f  = f x {-"~~."-}
```
之後我們討論其他的 |m| 時，也將把它們宣告為 |Monad| 的特例。
但這麼做只是為了兩個方便性：1. 讓不同的 |m| 可以共用 |return| 與 |(>>=)| 兩個符號，不用重新取名；2. 看到使用 |return| 與 |(>>=)| 的程式時，可以暫時不指定它們到底使用那一個特例。
若非為了這些小方便，單子與 type class 不一定得有關聯。

此外，Haskell 中的 type class 宣告也只保證 |return| 與 |(>>=)| 的型別是正確的。
目前 Haskell 並無法保證使用者定義的 |return| 與 |(>>=)| 滿足前述的單子律。

{title="副作用特定的運算子"}
不知讀者是否想起：那麼 |throw| 與 |catch| 呢？
他們也應該滿足一些性質，例如，|throw msg >>= f = throw msg| （拋出例外後，後面的 |f| 不會執行）和 |catch (throw msg) hdl = hdl msg| （|throw| 拋出的例外由 |hdl| 處理）應該都是合理以及必要的性質。
另一方面，它們是屬於「例外」這個副作用的運算子，其他的副作用並不見得會有它們。
反之，別的副作用可能會有該副作用的特定運算子。例如，要談可變變數，可能會有個賦值運算子，這是 |Except| 沒有的。

由此得知，用於表達副作用時，單子的運算子可分為兩大類：1. |return| 與 |(>>=)| 是各個副作用共通的，
每個單子都必須定義 |return| 與 |(>>=)|, 並確保它們滿足單子律。2. 此外，每個副作用還可能擁有特有的運算子，它們可能也有些該滿足的性質。
我們將在介紹各個副作用的小節中看到更多例子。

## 讀取單子 {#sec:monad-reader}
\index{side effect 副作用!reader 讀取}

為了進入下一個例子，我們為算式型別加上變數：
```spec
data Expr =  Num Int | Neg Expr | Add Expr Expr |
             Var Name | Let Var Expr Expr {-"~~,"-}

type Name = String {-"~~."-}
```
{.nobreak}|Name| 是變數名稱，|Var v| 是出現在算式中的變數，|Let| 則用來宣告新的區域變數。
例如，以下式子表達的是 |let x = 3 + 1 in (x+4)+x|:
```spec
Let "x" (Add (Num 3) (Num 1))
   (Add (Add (Var "x") (Num 4)) (Var "x")) {-"~~,"-}
```
{.nobreak}變數 |x| 的值為 |3+1|, 因此整個算式的值是 |((3+1) + 4) + (3+1) = 12|.

### 變數與環境 {#sec:var-env-reader}

有了變數後，我們不能只問「|Add (Var "x") (Var "y")| 的（整數）值是什麼」了，因為我們不知道 |x| 和 |y| 的值。
有自由變數的算式得放在一個*環境*下才能談它的值。
所謂「環境」是一個變數到值的函數，告訴我們每個變數的值。我們可以用一個串列表示：^[或著，我們也可以定義 |type Env = Name -> Maybe Int|, 而 |lookup env x = env x|.]
```spec
type Env = [(Name, Int)] {-"~~."-}
```
{.nobreak}例如 |Add (Var "x") (Num 4)| 在環境 |[("x", 3), ("y", 6)]| 下的值是 |7|.
我們也假設有一個「查表」函數：
```spec
lookup :: Env -> Maybe Int {-"~~."-}
```
{.nobreak}例如，當 |env = [("x", 3), ("y", 6)]|，|lookup env "x"| 是 |Just 3|，
|lookup env "z"| 則是 |Nothing|.

提醒一下讀者：|Let| 是在宣告區域變數，而不是賦值。例如，下式表達 |let x = 3 in x + (let x = 4 in x) + (-x)|：
```spec
Let "x" (Num 3)
    (Add (Add "x" (Let "x" (Num 4) (Var "x")))
         (Neg (Var "x")))
```
{.nobreak}
它的值是 |3 + 4 + (-3)|，而不是 |3 + 4 + (-4)|  --- 內層宣告的 |x| 僅是暫時遮蓋到外面的 |x|。

有了這些鋪陳，我們看看新的 |eval| 函數該怎麼寫。
既然算式要在環境之下才有值，|eval| 得把環境也納為參數之一：
```spec
eval :: Expr -> Env -> Int
```
{.nobreak}函數 |eval| 拿一個算式和一個環境，計算該算式的值。
新的 |eval| 中，最初的三個條款基本上是一樣的，只是多了一個參數 |env| 得往下傳：
```spec
eval (Num n)      env = n
eval (Neg e)      env = - (eval e env)
eval (Add e0 e1)  env = eval e0 env + eval e1 env {-"~~."-}
```
{.nobreak}碰到變數時，我們到環境中查變數的值：
```spec
eval (Var x) env = case lookup env x of Just v -> return v {-"~~."-}
```
{.nobreak}這裡的 |case| 算式只處理了 |Just| 的情形。
如果 |lookup| 傳回的是 |Nothing|，也就是變數 |x| 並不在環境 |env| 中，該怎麼辦呢？我們等下再談。
最後，碰到 |Let x e0 e1| 時，我們先把 |e0| 的值在 |env| 這個環境之下算出，然後算 |e1|:
```spec
eval (Let x e0 e1) env =
  let v = eval e0 env
  in eval e1 ((x, v) : env)
```
{.nobreak}但計算 |e1| 時須使用新的環境 |(x, v) : env|，這讓 |e1| 可以用到 |x|。變數 |x| 在新環境中的值是 |v|.

{title="算式的語意是函數"}
第 \@ref{sec:monad-bottom-up} 節開頭提及，
算式沒有變數、沒有除法時，|eval| 的型別是 |Expr -> Int| --- 此時一個算式的「意思」就是一個整數。
有了除法後，為了表示可能拋出例外的函數，|eval| 的型別變成 |Expr -> Except Int|.
此時 |Except a| 代表一個尚待完成、可能有副作用（拋出例外）的計算。

加上變數、考慮環境後， |eval| 的型別變成了 |Expr -> (Env -> Int)|：|eval| 拿一個算式，傳回一個函數；該函數又拿一個環境，才算出一個整數值。
也就是說，一個算式的語意是「拿一個環境，傳回一個整數的函數」。
的確，既然算式算成的那個整數必須由環境決定，算式其實不能看作一個數值，而應該是從環境到整數的函數才對。
算式 |eval (Add (Var "x") (Var "y"))| 是一個函數，如果給它 |[("x", 3), ("y", 2)]|, 我們得到 |5|;
如果給 |[("x",4), ("y", -3)]|, 我們得到 |1|.

如果把「給一個環境，傳回型別為 |a| 的結果的函數」叫做 |Reader a|, 也就是說定義 |type Reader a = Env -> a|，
函數 |eval| 的型別成了 |Expr -> Reader a|.
此處，|Reader a| 也可視為一個*尚待完成、可能發生副作用的計算*。
此處可能的副作用包括「和環境詢問變數的值」。
習慣上，我們把這種副作用稱作「讀者(reader)」或「讀取」。
「給環境」的動作，就是執行運算，把值算出來。
我們把其中兩個條款改寫成 $\lambda$ 算式：
```spec
eval (Num n)      = \env ->  n
eval (Add e1 e2)  = \env -> eval e1 env + eval e2 env
```
{.nobreak}可以理解成：|eval (Num n)| 傳回一個計算，無論環境為何，該計算都傳回 |n|;
|eval (Add e1 e2)| 也傳回一個計算，該計算拿到環境後，在同一個環境之下把 |eval e1| 和 |eval e2| 算成值，然後傳回他們的和。

然而，手動把 |env| 傳來傳去是個重複性高、容易出錯、也嫌累贅的動作。在第 \@ref{sec:exceptions} 節中，我們把重複性地產生與拆開 |Except| 型別的動作抽象成 |return| 和 |(>>=)|，
使得 |Except| 成為一個單子。
對於本節的 |Reader|, 我們也能設計出一組 |return| 和 |(>>=)|, 把重複的動作抽象掉，使得 |Reader| 成為一個單子嗎？

### 「讀取」副作用是單子 {#sec:reader-is-monad}

{title="讀取單子"} 如第 \@ref{sec:monad-class-laws} 節所述，
|return| 製作一個沒有副作用的計算，|(>>=)| 則用於把兩個計算接起來。
把 |m| 代換成 |Reader|, 它們的型別分別是：
```spec
return  :: a -> Reader a
(>>=)   :: Reader a -> (a -> Reader b) -> Reader b {-"~~,"-}
```
{.nobreak}其中 |Reader a = Env -> a|.

函數 |return| 比較單純：|return x| 是一個無論 |env| 是什麼，都傳回 |x| 的計算：
```spec
return x env = x {-"~~."-}
```
{.nobreak}至於 |m >>= f| 則可定義如下：
```spec
(p >>= f) env = f (p env) env {-"~~."-}
```
{.nobreak}|p >>= f| 的型別為 |Reader b|, 意謂它可以收一個環境 |env| 當參數，而等號右手邊必須算出一個型別為 |b| 的結果。
變數 |p :: Reader a| 是一個尚待完成的計算，|p env| 把它算出來，得到型別為 |a| 的結果。
函數 |f| 的型別為 |a -> Reader b|, 因此 |f (p env)| 意謂 |f| 得到 |p env :: a| 的結果，並*算出一個新的計算*. 這個計算又在得到 |env| 之後才真正被算出來，最後型別為 |b|.


有了 |return| 與 |(>>=)|, |eval| 的前三個條款可改寫如下：
```spec
eval :: Expr -> Reader Int
eval (Num n)      =  return n
eval (Neg e)      =  eval e >>= \v -> return (-v) {-"~~."-}
eval (Add e0 e1)  =  eval e0  >>= \v0 ->
                     eval e1  >>= \v1 ->
                     return (v0 + v1) {-"~~,"-}
```
{.nobreak}除了 |Except| 變成 |Reader| 之外和第 \@ref{sec:exceptions} 節完全相同！
由於使用了單子這個適當的抽象，只要把型別從 |Except| 變成 |Reader|，主程式在不需大幅更動的情況下就可以沿用。使用單子，我們能*模組化地挑選我們想要的副作用*。

{title="讀取單子的特定運算"}
本節新添加的 |Var| 與 |Let| 兩個情況是第 \@ref{sec:exceptions} 節沒有的。
要處理它們，需要讀取副作用特有的運算子。

處理 |Var x| 時，|eval| 得到環境中查變數 |x| 的值。
我們姑且先為此專門定義一個函數：
```spec
lookupVar :: Var -> Reader Int
lookupVar x env = case lookup env x of Just v -> return v {-"~~,"-}
```
{.nobreak}之後再考慮更通用的情況。
有了它，|eval| 遇上 |Var x| 的條款可寫成：
```spec
eval (Var x) = lookupVar x {-"~~."-}
```

計算 |Let x e1 e2| 時，我們需要更動環境，把「|x| 的值是 |e1| 的值」這個資訊加到環境中，
並在新環境內執行 |eval e2|, 但執行完之後就回到原有的環境 --- 新環境只是局部的。
由於這是常見的模式，我們可定義一個更通用的運算子。
給定一個函數 |f :: Env -> Env| 用於製作局部的環境，
如果目前的環境是 |env|, 算式 |local f p| 在新環境 |f env| 之下執行 |p|:
```spec
local :: (Env -> Env) -> Reader a -> Reader a
local f p env = p (f env) {-"~~."-}
```
有了 |local| 的幫忙，|eval| 遇上 |Let| 時可寫成：
```spec
eval (Let x e0 e1) =  eval e0 >>= \v ->
                      local ((x,v):) (eval e1) {-"~~."-}
```
我們用 |((x,v):)| 幫環境增加一筆資料，在這之下計算 |eval e2|.


:::{.exlist}
:::{.exer #ex:expand-reader-by-def}
使用本節的定義，將 |eval (Add e0 e1) env| 與 |eval (Let x e0 e1) env| 展開，確認它們和第 \@ref{sec:var-env-reader} 節的定義一樣。意即：
```spec
eval (Add e0 e1)    env = eval e0 env + eval e1 env {-"~~,"-}
eval (Let x e0 e1)  env = eval e1 ((x, eval e0 env):env)  {-"~~."-}
```
:::
:::{.exans}
考慮 |eval (Add e0 e1)|:
```spec
     eval (Add e0 e1) env
===     {- |eval| 之定義 -}
     (eval e0  >>= \v0 -> eval e1  >>= \v1 -> return (v0 + v1)) env
===     {- |(>>=)| 之定義 -}
     (\v0 -> eval e1 >>= \v1 -> return (v0 + v1)) (eval e0 env) env
===     {- 函數應用 -}
     (eval e1 >>= \v1 -> return (eval e0 env + v1)) env
===     {- |(>>=)| 之定義, 函數應用 -}
     return (eval e0 env + eval e1 env) env
===     {- |return| 之定義 -}
     eval e0 env + eval e1 env {-"~~."-}
```

考慮 |eval (Let x e0 e1) env|:
```spec
     eval (Let x e0 e1) env
===     {- |eval| 之定義 -}
     (eval e0 >>= \v -> local ((x,v):) (eval e1)) env
===     {- |(>>=)| 之定義, 函數應用 -}
     local ((x,eval e0 env):) (eval e1) env
===     {- |local| 之定義 -}
     eval e1 ((x, eval e0 env):env)  {-"~~."-}
```
:::
:::

{title="更通用的環境單子"}
為了說明方便，目前為止我們假設「環境」是某個固定的型別: |Env|.
我們當然可以把這部份也抽象掉：
```spec
type Reader e a = e -> a  {-"~~."-}
```
{.nobreak}現在 |Reader| 多吃一個參數 |e|, 代表環境的型別。
對任意的 |e|, |Reader e| 都是一個單子，
函數 |local| 更通用的型別是 |(e -> e) -> Reader e a -> Reader e a|.
本節之前的每個 |Reader| 都需代換成 |Reader Env|.
例如 |eval| 的型別是 |Expr -> Reader Env Int|.
但改變的都只有型別，程式不需變動。

函數 |lookupVar :: Var -> Reader Env Int| 只能在 |e| 為 |Env| 的情況下運作。
更一般來說，讀取單子通常會有一個運算子 |ask|, 把整個環境傳出來供我們使用：
```spec
ask :: Reader e e
ask env = env {-"~~."-}
```
{.nobreak}函數 |lookupVar| 則可改用 |ask| 定義為：
```spec
lookupVar :: Var -> Reader Int
lookupVar x =  ask >>= \env ->
               case lookup env x of Just v -> return v {-"~~."-}
```

最後，本節之中讓 |Reader e| 與前一節的 |Except| 共用 |return|, |(>>=)| 等符號。
若需在 Haskell 中如此，我們得將 |Reader e| 宣告為 type class |Monad| 的一個特例。
但由於一些型別檢查的技術問題， Haskell 不允許用 |type| 宣告的別名成為 type class 特例。
我們得把 |Reader| 用 |data| 宣告成一個資料型別：^[更普遍的做法是用 |newtype| 宣告：|newtype Reader e a = Reader { runReader :: (e -> a) }|. 但本書不談 |newtype|.]
```spec
data Reader e a = Reader (e -> a) {-"~~,"-}

instance Monad (Reader e) where
    return a        = Reader (\e -> a)
    Reader r >>= f  = Reader (\e -> f (r e) e) {-"~~."-}
```

### 推論讀取單子程式的性質 {#sec:monad-reader-laws}

給一個單子程式，如何討論它的性質？
比如說，對某一個 |e|, 如何得知 |eval| |(Let "x" (Num 3)| |(Let "y" (Num 4) e))|
的值是什麼？
它和 |eval| |(Let "y" (Num 4)| |(Let "x" (Num 3) e))| 的值是否總是相等？

由於 |eval| 是用 |return|, |(>>=)|, |local| ... 等等運算子定義出來的，而這幾個運算子的定義也都已經有了，
我們總是可以把他們的定義都展開，
回到最基礎的層次證明任何我們想確認的性質。
但一來如此的證明可能非常瑣碎，二來 |return|, |(>>=)| 等運算子的定義可能還會改變。
我們是否能在稍微抽象一點的層次運作，假裝我們不知道這些單子運算子的定義，只討論它們具有什麼性質，並用這些性質來做證明？

我們應可以合理要求一個「正確」的讀取單子實作應該要滿足下列的性質。
首先，假設 |e| 是一個不含變數 |v| 的算式：
```{.equation #eq:reader-ask-return}
|ask >>= \v -> return e = return e {-"~~,"-}| \mbox{如果 |v| 不出現在 |e| 之中。}
```
{.nobreak}等號兩邊都只是傳回 |e| 的值，而 |e| 的值不受 |v| 影響，因此 |ask| 是可以省略掉的。
其次，連續使用 |ask| 兩次可以縮減為一次就好：
```{.equation #eq:reader-ask-ask}
|ask >>= \v0 -> ask >>= \v1 -> f v0 v1 {-"~~"-}={-"~~"-} ask >>= \v -> f v v {-"~~."-}|
```
在等號左手邊，我們把問了環境兩次之後的計算抽象為一個函數呼叫 |f v0 v1|.
在右手邊我們則讓 |f| 的兩個參數都是 |v| --- 詢問環境一次的結果。

下面兩個式子討論當 |local| 遇上 |return| 與 |(>>=)| 時會如何：
:::{.equations}
  * {#eq:reader-local-return} |local g (return e)| |= return e|
  * {#eq:reader-local-bind} |local g (p >>= f)| |= local g p >>= (local g . f)|


:::
{.nobreak}在 \@eqref{eq:reader-local-return} 的左手邊，改變環境之後立刻 |return e|, 其實和單純做 |return e| 一樣。
性質 \@eqref{eq:reader-local-bind} 則告訴我們 |local g| 可以分配到 |(>>=)| 的兩側。由於型別之故，|(>>=)| 的左邊是 |local g p|, 右邊則得用函數合成 |(.)|.

最後，下列性質將 |local| 與 |ask| 關聯在一起：
```{.equation #eq:reader-local-ask}
|local g ask = ask >>= (return . g) {-"~~."-}|
```
{.nobreak}在 |local g| 的環境之下做 |ask|, 相當於先做 |ask|, 然後把得到的環境交給 |g| 加工。
我們可說算式 \@eqref{eq:reader-local-ask} 藉由這兩個運算子的互動定義出了 |local| 的「意思」。

有了這些性質，我們不需引用 |local|, |ask|, |(>>=)| ... 等等的定義，也可論證讀取單子程式的性質了。例如，我們來看看 |let x = 4 in x + x| 的值會是什麼：
```spec
     eval (Let "x" (Num 4) (Add (Var "x") (Var "x")))
===    {- |eval| 之定義 -}
     eval (Num 4) >>= \v -> local (("x",v):) (eval (Add (Var "x") (Var "x")))
===    {- |eval| 之定義 -}
     return 4 >>= \v -> local (("x",v):) (eval (Add (Var "x") (Var "x")))
===    {- 單子律：左單位律 \eqref{eq:monad-left-id} -}
     local (("x",4):) (eval (Add (Var "x") (Var "x")))
===    {- |eval| 之定義 -}
     local (("x",4):) (  eval (Var "x") >>= \v0 ->
                         eval (Var "x") >>= \v1 -> return (v0 + v1))
===    {- \eqref{eq:reader-local-bind} -}
     local (("x",4):) (eval (Var "x")) >>= \v0 ->
     local (("x",4):) (eval (Var "x")) >>= \v1 ->
     local (("x",4):) (return (v0 + v1))
```
{.nobreak}我們將 |local (("x",4):) (eval (Var "x"))| 抽出來化簡：
```spec
    local (("x",4):) (eval (Var "x"))
===   {- |eval| 與 |lookupVar| 之定義 -}
    local (("x",4):) (ask >>= \env -> case lookup env "x" of Just v -> return v)
===   {- \eqref{eq:reader-local-bind} -}
    local (("x",4):) ask >>= \env ->
    local (("x",4):) (case lookup env "x" of Just v -> return v)
===   {- \eqref{eq:reader-local-ask}, 左單位律 \eqref{eq:monad-left-id} -}
    local (("x",4):) (case lookup (("x",4):env) "x" of Just v -> return v)
===   {- |lookup (("x",4):env) "x" = Just 4| -}
    local (("x",4):) (return 4)
===   {- \eqref{eq:reader-local-return} -}
    return 4 {-"~~."-}
```
{.nobreak}由此我們得知 |local (("x",4):) (eval (Var "x"))| 就是 |return 4|.
將它放回原式中：
```spec
     local (("x",4):) (eval (Var "x")) >>= \v0 ->
     local (("x",4):) (eval (Var "x")) >>= \v1 ->
     local (("x",4):) (return (v0 + v1))
===   {- 前述計算 -}
     return 4 >>= \v0 -> return 4 >>= \v1 -> return (v0 + v1)
===   {- 單子律：左單位律 \eqref{eq:monad-left-id} -}
     return (4 + 4) {-"~~."-}
```
{.nobreak}因此，|eval (Let "x" (Num 4) (Add (Var "x") (Var "x")))| 就是 |return 8|.

提醒讀者注意一點：|eval (Let "x" (Num 4) (Add (Var "x") (Var "x")))| 和 |return 8| 都不是基礎型別，而是「尚待完成的計算」。
論證單子程式時我們常常不是在基礎型別的層次上運作，而是證明一個計算與另一個計算是等價的。
這意味著它們傳回同樣的值，也發生同樣的副作用。
我們日後會看到更多此類的例子。

:::{.exlist}
:::{.exer}
證明對所有 |e :: Expr|,
```spec
  eval (Let "x" (Num 3) (Let "y" (Num 4) e)) =
    eval (Let "y" (Num 4) (Let "x" (Num 3) e)) {-"~~,"-}
```
如果 |(("x",3):) . (("y",4):) = (("y",4):) . (("x",3):)| 成立。
:::
:::{.exer}
然而，|(("x",3):) . (("y",4):) = (("y",4):) . (("x",3):)| 並不成立。
:::
:::

我們稍早曾遇到這個問題：如果給這樣的式子 |eval (Var "x") [("y",0)]|,
變數 |x| 並不在環境中，|lookup| 將傳回 |Nothing|，這時該怎麼辦？

我們可以再擴充 |Reader| 的型別，讓 |eval| 也可以傳回一個 |Except| 結果：
```spec
type ReaderExcept e a = e -> Except a
```
而 |return| 和 |(>>=)| 也得隨之擴充：
```spec
return a = \env -> Just a
rm >>= f = \env -> case rm env of
                    Just v -> f v env
                    Nothing -> Nothing
```
這個 |ReaderExcept| 型別綜合了讀取單子與例外單子的功能，其 |return| 與 |(>>=)| 定義也像是兩個單子定義的混合。
但這並不是令人相當滿意的做法。|ReaderExcept| 比起 |Reader| 又更複雜了一點。日後我們也許會想要有更多功能，例如狀態、輸出入等。|ReaderExcept| 已經夠抽象難解了，我們並不希望設計、維護越來越龐大的單子。

既然 Maybe 單子讓一個程式加上「例外」的副作用，讀取單子讓一個程式加上可存取環境的功能，我們能否把這兩項功能分別模組化地加入呢？

也就是說，給了兩個單子 M1 和 M2, 能否把他們的功能加在一起，產生另一個新單子呢？

## 狀態單子 {#sec:monad-state}
\index{side effect 副作用!state 狀態}

沿用第 \@ref{sec:exceptions} 節之中的型別：
```spec
data Expr = Num Int | Neg Expr | Add Expr Expr | Div Expr Expr  {-"~~."-}
```
{.nobreak}這次我們暫且忽略分母為零的可能，而考慮另一個應用：我們想知道計算過程中做了多少次除法。
指令式語言中，一個常見的作法是用一個可變變數來計數。
在函數語言中我們怎麼模擬這種行為呢？

在指令式語言中，可變變數的值常用來表示整個系統目前的「狀態(state)」：諸如已處理過的資料個數、處理中的元素號碼、棋盤上每個棋子的位置... 等等。因此我們把「存取可變變數」的能力稱作*狀態*(*state*)副作用。

經過前幾節的熟悉，我們現在應可以更抽象地、*由上而下*地想像單子了：對於一個我們需要的副作用，先假設其單子存在，考慮它該有哪些運算子、這些運算子該滿足什麼性質、用它們如何寫程式。
然後才考慮這個單子的實作。對於狀態這個副作用，我們該怎麼設計其運算子呢？

在命令式語言中，|x := x + 1| 這行指令把可變變數 |x| 的值遞增。這一行看似單純的指令其實包含幾項特性：
  * 變數是有名字的；
  * 當變數名字出現在 |:=| 的右手邊，表示讀取變數的值；
  * 當變數名字出現在 |:=| 的左手邊，表示將值寫入該變數。


{.nobreak}函數語言中討論狀態副作用時偏好用單純些、使用時比較繁瑣、但比較好討論性質的設計：變數沒有名字，並且把「讀取」與「寫入」兩個動作分為單獨的運算子。

具體說來，令 |State s a| 表示一個結果型別為 |a|, 但在執行時可讀寫一個型別為 |s| 的可變變數的計算。我們要求 |State s| 是一個單子 --- 意謂存在著滿足單子律的
|return :: a -> State s a| 和 |(>>=) :: State s a -> (a -> State s b) -> State s b|。
一個型別為 |State s a| 的運算中隱藏的可變變數沒有名字，只能用下述兩個運算子存取：
```spec
get  :: State s s  {-"~~,"-}
put  :: s -> State s () {-"~~."-}
```
{.nobreak}運算子 |get| 和第 \@ref{sec:monad-reader} 節中的 |ask| 類似，讀出該可變變數的值；|put e| 則把 |e| 的值寫到可變變數中，並傳回 |()|。
例如，當 |s = Int|, 我們可以定義如下的操作 |inc|，把可變變數加一：
```spec
inc :: State Int ()
inc = get >>= \v -> put (1+v) {-"~~."-}
```

關於 |put| 有幾件事情可提醒。首先，當我們呼叫 |put e|, 其中的 |e| 已經是一個型別為 |s| 的純數值，不含副作用。
例如在 |inc| 之中，我們必須先將變數的值 |get| 出來（這是一個有副作用的動作），才能計算新的值並寫回去。
這讓程式寫起來很繁瑣，但也使得推論程式的性質容易許多。
其次，關於 |put e| 的型別 |State s ()|. 回想：|()| 是一個只有一個值的型別，該值在 Haskell 中也寫作 |()|. 給定 |e :: s| 後，|put e :: State s ()| 是一個會存取型別為 |s| 的可變變數，並傳回 |()| 的計算。在此，「傳回 |()|」可理解為傳回一個不帶資訊的值，僅表達「我做完了」。

這個傳回值既然沒有資訊，通常不會被用上。因此當 |put| 不是函數的最後一個動作時，程式常有如下的模樣：
```spec
   ... put e >>= \_ -> ...
```
{.nobreak}由於「執行一段程式，但只需要它的副作用，不需要它的結果」這件事在本章還會常常發生，我們另外訂一個運算元：
```spec
(>>) :: m a -> m b -> m b
p >> q = p >>= \_ -> q {-"~~."-}
```
{.nobreak}如此一來 |put e >>= \_ -> q| 可以簡寫成 |put e >> q|.
（注意： |p >> q| 並不要求 |p| 的傳回值型別為 |()|.）

回到 |get| 與 |put|。
如果它們的某個實作確實表達了我們前面口述的意圖，該實作應該會滿足以下的規則：
:::{.equations}
  * {title="get-put:" #eq:state-get-put}
    |get >>= put| |= return () {-"~~,"-}|
  * {title="put-get:" #eq:state-put-get}
    |put e >> get| |= put e >> return e {-"~~,"-}|
  * {title="put-put:" #eq:state-put-put}
    |put e0 >> put e1| |= put e1 {-"~~,"-}|


:::
{.nobreak}以及一個和第 \@ref{sec:monad-reader} 節中的 |ask| 類似的性質：
```{.equation title="get-get:" #eq:state-get-get}
|get >>= \v0 -> get v1 >>= \v1 -> f v0 v1 {-"~"-}={-"~"-} get >>= \v -> f v v {-"~~."-}|
```
{.nobreak}其中，**get-put** 意謂：將可變變數的值讀出後立刻寫入相當於什麼都不做。
規則 **put-get** 意謂：剛做完 |put e| 之後立刻讀取可變變數的值，必定得到 |e|.
規則 **put-put** 意謂：連做兩個 |put| 之後，只有第二個 |put| 寫入的值會被留下。
規則 **get-get** 則意謂：連做兩次 |get| 所得到的值必定相同，可以只 |get| 一次就好。

如前所述，用 |get| 與 |put| 可定義出 |inc|, 而我們只需在 |eval| 遇到 |Div| 的情況中呼叫 |inc|，就可記錄做了多少次除法了：
```spec
eval (Div e0 e1) =  eval e1  >>= \v1 ->
                    eval e0  >>= \v0 ->
                    inc >>
                    return (v0 `div` v1) {-"~~."-}
```
{.nobreak}函數 |eval| 的其他條款可完全不變，只需把所用單子的型別改成 |State Int|.
由於單子捕捉了含副作用的程式的共通模式，我們只需選用不同的副作用運算子，就可在不更動大部分程式的情況下使用我們需要的副作用。

### 河內塔問題 {#sec:hanoi}

本節以河內塔問題為例子，示範狀態單子的推論。

```spec
hanoi 0        = return ()
hanoi (Suc n)  = hanoi n >> inc >> hanoi n {-"~~."-}
```

|hanoi n = put (2^n -1)|.

## 參考資料

@Wadler:92:Monads
