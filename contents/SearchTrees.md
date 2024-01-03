
# 搜尋樹 {#ch:induction-search-trees}

本章以搜尋樹為例，示範樹狀結構上的歸納證明。本章於初次閱讀時可跳過。

許多應用需要將資料收集在某種表達「集合」的資料結構中。
我們希望能做的操作包括：尋找並判斷某筆資料是否在集合中、加入某筆新資料、刪除某筆資料，等等。
許多演算法都仰賴這些操作能有效率地被實作。

我們可以用串列表達一個集合，但在一般的簡單實作中，在串列中尋找與刪除都需要與串列長度成正比的時間。若集合中的資料是能比大小的，使用一個陣列並將元素排序好，可用二元搜尋法在對數時間內尋找某筆資料。但在陣列中加入與刪除元素也都需要與陣列長度成正比的時間挪出或消除空位。

因此，許多針對此類應用的樹狀結構被發展出來。

## 二元搜尋樹 {#sec:induction-binary-search-tree}

*二元搜尋樹*(*binary search tree*)\index{binary search tree 二元搜尋樹}是一類樹狀資料結構的統稱。簡單的二元搜尋樹是一種類似 |ITree| 的結構（為說明方便，我們讓樹中的元素皆為 |Int|）：
```haskell
data BTree = Nul | Nod BTree Int BTree {-"~~,"-}
```
{.nobreak}另有個附加限制：在所有內部節點 |Nod t x u| 中，|t| 之中的所有元素均小於 |x|, |u| 之中的所有元素均大於 |x|.
以下我們將此限制簡稱為「有序性」。
給定一個有序的二元搜尋樹 |t|，下述函數 |search k t| 判斷 |k| 是否出現在 |t| 之中：
```haskell
search :: Int -> BTree -> Bool
search k Nul          = False
search k (Nod t x u)  | k < x   = search k t
                      | k == x  = True
                      | x < k   = search k u {-"~~."-}
```
{.nobreak}這是一個歸納定義。由於有序性，每遇到一個 |Nod t x u| 節點，我們可比較 |k| 與 |x| 的大小，藉以決定往哪一個子樹做搜尋。

如果二元樹是*平衡*的 --- 意指在樹中的每個 |Nod t x u| 之中，|t| 和 |u| 的元素數目大致相等，或著至少其比例為某個常數，|search k (Nod t x u)| 每次選擇往 |t| 或 |u| 搜尋時都會排除一定比例的元素。如此一來，搜尋一個含 |n| 個元素的樹可在 $O(\log n)$ 的時間內完成。
然而，維持「平衡」並不容易，也是各種二元搜尋樹各顯神通之處。

以下我們多給一些定義，以便更形式化地描述有序性。我們假設有個抽象的「集合」型別 |Set a|. 含單一元素 |x| 的集合寫成 |singleton x|; 聯集寫作 |(`union`)|, 並具有結合律、交換律等性質。下述函數 |elems| 傳回一個樹中的所有元素（類似練習 \@ref{ex:ITree-tags} 中的 |tags|）：
```haskell
elems :: BTree -> Set Int
elems Nul          = []
elems (Nod t x u)  = elems t `union` singleton x `union` elems u {-"~~."-}
```
{.nobreak}有序性可表示為下列述語 |sorted|:
```haskell
sorted :: BTree -> Bool
sorted Nul          =  True
sorted (Nod t x u)  =  all (<x) (elems t) && all (x<) (elems u) &&
                       sorted t && sorted u {-"~~."-}
```
{.nobreak}其中 |all :: (a -> Bool) -> Set a -> Bool| 檢查一個集合中的元素是否均滿足某述語。函數 |all| 滿足以下性質：
```spec
all p empty          = True
all p (singleton x)  = p x
all p (s `union` t)  = all p s && all p t {-"~~."-}
```

在二元搜尋樹中插入新元素的函數可定義如下：
```haskell
insert :: Int -> BTree -> BTree
insert k Nul          = Nod Nul k Nul
insert k (Nod t x u)  | k < x   = Nod (insert k t) x u
                      | k == x  = Nod t x u
                      | x < k   = Nod t x (insert k u) {-"~~."-}
```
{.nobreak}函數 |insert| 和 |search| 的結構很類似：都藉由比較 |k| 與 |x| 決定該往哪兒插入元素；函數 |search| 只在碰到 |Nul| 時才能傳回 |False|, 函數 |insert k| 也只將 |Nod Nul k Nul| 放在原本 |Nul| 出現之處 --- 新插入的節點永遠是最邊緣的葉節點。

我們自然會希望 |insert| 保持有序性：如果 |t| 是有序的，|insert k t| 也應該是。表示為定理如下：
:::{.theorem}
對所有 |t| 與 |k|, |sorted t ==> sorted (insert k t)|.
:::
:::{.proof}
在 |t| 之上做歸納證明。
基底情況 |t := Nul| 之中，|sorted (Nod Nul k Nul)| 顯然成立。
歸納情況有 |k < x|, |k == x|, |x < k| 三種。
以下我們只列出第一種。

{.nobreak}**狀況** |t := Nod t x u|, |k < x|:
```haskell
     sorted (insert k (Nod t x u))
<=>   {- |insert| 之定義, |k < x| -}
     sorted (Nod (insert k t) x u)
<=>   {- |sorted| 之定義 -}
     all (<x) (elems (insert k t)) && all (x<) (elems u) &&
     sorted (insert k t) && sorted u
<=>   {- 練習 \ref{ex:elems-insert}: |elems (insert k t) = singleton k `union` elems t| -}
     all (<x) (singleton k `union` elems t) && all (x<) (elems u) &&
     sorted (insert k t) && sorted u
<=>   {- |all| 之性質 -}
     k < x && all (<x) (elems t) && all (x<) (elems u) &&
     sorted (insert k t) && sorted u
<==   {- |k < x|, 歸納假設 -}
     all (<x) (elems t) && all (x<) (elems u) &&
     sorted t && sorted u
<=>   {- |sorted| 之定義 -}
     sorted (Nod t x u) {-"~~."-}
```
:::

函數 |insert| 並不保證做出的樹能平衡 --- 恰恰相反，我們一不小心便會做出偏一邊的樹。例如，
|insert 5 (insert 4 (insert 3 (insert 2 (insert 1 Nul))))|
得到的結果會是：
```spec
  Nod Nul 1 (Nod Nul 2 (Nod Nul 3 (Nod Nul 4 (Nod Nul 5 Nul)))) {-"~~."-}
```
{.nobreak}在這個樹中搜尋 |5|, 和在串列 |[1,2,3,4,5]| 之中尋找 |5| 基本上是一樣的。

許多建立在二元搜尋樹的進階資料結構會在插入元素時多做些操作，想辦法維持樹的平衡。
我們將在第\@ref{sec:induction-red-black-tree}節介紹的紅黑樹就是一個例子。

:::{.exlist}
:::{.exer #ex:elems-insert}
證明對所有 |t| 與 |k|, |elems (insert k t) = singleton k `union` elems t|.
:::
:::

## 紅黑樹 {#sec:induction-red-black-tree}

在二元搜尋樹的基礎上，*紅黑樹*(*red-black tree*)\index{red-black tree 紅黑樹}多加了個屬性：每個節點都是紅色或黑色之一。
表示成 Haskell 資料結構如下：
```hasekell
data RBTree = E  | R RBTree Int RBTree
                 | B RBTree Int RBTree {-"~~,"-}
```
{.nobreak}其中 |E| 為沒有資料的葉節點，|R| 為紅色內部節點，|B| 為黑色內部節點 --- 葉節點 |E| 被視為黑色的。
定義 |data Color = Red || Blk|, 下述定義的 |color t| 傳回 |t| 的根部節點的顏色：
```{.haskell .invisible}
data Color = Red | Blk {-"~~,"-}
```
```haskell
color :: RBTree -> Color
color E          = Blk
color (R _ _ _)  = Red
color (B _ _ _)  = Blk {-"~~."-}
```
{.nobreak}我們要求紅黑樹滿足下列性質：

  1. 紅黑樹也是二元搜尋樹，意即它得是有序的。
  2. 從根部開始到每個葉節點 |E| 的路徑上的黑節點數目均相同。我們說這樣的一棵樹是*平衡*的。
  3. 紅節點的兩個子代都必須是黑色的，黑節點則無此限制。為方便說明，我們把滿足此條件的樹稱為*準紅黑樹*。
  4. 根節點為黑色的。

{.nobreak}其中，關於有序性的討論和前一節原則上相同，此節將之省略。我們假設存在某函數 |sorted :: RBTree -> Bool| 判斷一棵紅黑樹是否有序。
我們看看其他性質如何形式化。

首先，函數 |bheight| 定義一棵樹的「黑高度」 --- 所有路徑上黑色節點的最多數目：
```haskell
bheight :: RBTree -> Nat
bheight E          = 0
bheight (R t x u)  = bheight t `max` bheight u
bheight (B t x u)  = 1 + (bheight t `max` bheight u) {-"~~."-}
```
{.nobreak}說一棵樹「平衡」意指每個內節點中，兩個子樹的黑高度均相等。
```haskell
balanced :: RBTree -> Bool
balanced E          =  True
balanced (R t x u)  =  bheight t == bheight u && balanced t && balanced u
balanced (B t x u)  =  bheight t == bheight u && balanced t && balanced u {-"~~."-}
```

函數 |semiRB| 檢查一棵樹是否為準紅黑 --- 紅節點的兩棵子樹均為黑色：
```haskell
semiRB :: RBTree -> Bool
semiRB E          =  True
semiRB (B t x u)  =  semiRB t && semiRB u
semiRB (R t x u)  =  color t == Blk && color u == Blk && semiRB t && semiRB u
```
{.nobreak}最後，如前所述，紅黑樹需滿足 |sorted|, |balanced|, |semiRB|, 並且根節點須為黑色：
```spec
redBlack :: RBTree -> Bool
redBlack t =  sorted t && balanced t && semiRB t && color t == Blk {-"~~."-}
```

在這樣一棵二元樹中，由於 |balanced| 被滿足，每條路徑上的黑節點數目均相同；由於 |semiRB| 被滿足，紅節點不會連續出現。因此最長路徑之長度不超過最短路徑的兩倍。在這樣的樹中做二元搜尋，總會在 $O(\log n)$ 的時間內找到資料或走到葉節點。

### 紅黑樹插入

在紅黑樹中插入元素的方式最初和二元搜尋樹相同：一邊搜尋一邊往下走，如果我們碰到 |E|, 便是插入新元素之處。新元素總在邊緣被插入，而樹的有序性仍保持著。

新加入的節點該是什麼顏色呢？讓新節點為紅色可能是個合理選擇。如此一來，插入新元素不會改變一棵樹的黑高度，也因此如果該樹原本是平衡的，加入新節點後的新樹仍是平衡的。

但這麼做可能破壞準紅黑性質：路徑上有可能出現兩個連續的紅節點。
因此我們在插入後的*回程*途中適時做*旋轉*，如圖\@ref{fig:red-black-rotate}所示。
每當我們看到一個黑節點之下有兩個連續的紅節點，必定是圖中四個角落的四種情形之一（我們只插入了一個元素，最多只有一個多出的紅節點。圖中 |s|, |t|, |u|, 與 |v| 仍是平衡的準紅黑樹）。
我們將每個情形都旋轉成圖中央的情況。
如此一來圖中央以 |x|, |z| 為根部的兩顆子樹都是黑根部的紅黑樹，|y| 是紅節點。
於是我們再往上檢查，如果又出現四種情況之一就再旋轉，否則往上重建路徑，直到回到根部。
如此做出一棵滿足準紅黑性質的樹。
最後，如果根部節點為紅色，便直接改成黑色。

::: {.figure .top title="在紅黑樹中插入新元素後做的四種旋轉。" #fig:red-black-rotate}
::: {.center}
```texonly
\includegraphics[width=0.6\textwidth]{Pics/red-black-rotate.pdf}
```
:::
:::

我們看看前述的插入演算法可如何表示為 Haskell 程式。
我們將主要執行插入與旋轉的函數稱為 |ins :: Int -> RBTree -> RBTree|.
函數 |insert| 則在呼叫 |ins| 之後將樹根改為黑色的：
```haskell
insert :: Int -> RBTree -> RBTree
insert k t = blacken (ins k t) {-"~~,"-}
  where  blacken (R t x u) = B t x u
         blacken t = t {-"~~."-}
```

:::{.infobox title="紅黑樹旋轉只需四種情況"}
本節的的紅黑樹旋轉方式來自 @Okasaki:99:RedBlack。
熟悉資料結構的讀者可能發現它們比一般教科書或網路資源中的處理方式簡單許多：
一般資料中常會分出八種以上的狀況，除了主要路徑上的三個節點，也會考慮其兄弟節點的顏色。

Okasaki 發現只需本節的這四種情況就足夠了。
讀者也應可發現，採用較簡單的版本，對於證明以及暸解紅黑樹的性質幫助很大。

那麼，為何一般教科書會用上那麼多情況呢？
Okasaki 認為可能是效率考量。
一般書中的版本中，有些情況可不需旋轉，只直接改變節點顏色。
如此一來需要更動的欄位數目較少。
有些情況中轉出的樹根部已是黑色的。在指令式語言中，此時該程序就可以直接結束。

然而，在函數語言中，我們無論如何都需重建整個路徑上的節點。
因此上述優點均不明顯。
另一方面，Okasaki 也認為此種情況較少的版本是比較適合用於教學中的。
:::



函數 |ins| 在遇上紅節點（|R t x u|）時和第\@ref{sec:induction-binary-search-tree}中的 |insert| 很類似：比較 |k| 與 |x| 以決定該往哪邊插入，
並在歸納呼叫後以 |R| 重做節點。
但遇到黑節點 |B t x u| 時，我們不使用 |B|, 而是額外呼叫 |rotate| 函數：
```haskell
ins :: Int -> RBTree -> RBTree
ins k E = R E k E
ins k (R t x u)  | k <  x  = R (ins k t) x u
                 | k == x  = R t x u
                 | k >  x  = R t x (ins k u)
ins k (B t x u)  | k <  x  = rotate (ins k t) x u
                 | k == x  = B t x u
                 | k >  x  = rotate t x (ins k u) {-"~~."-}
```
{.nobreak}回顧：圖\@ref{fig:red-black-rotate}的四種旋轉都只在根節點為黑色時啟動，因此我們也只在碰上黑節點時呼叫 |rotate|。
在 |rotate s x t| 之中，|s| 為目前的左子樹，|x| 為目前的（黑色）節點中的標籤，
|t| 則為目前的右子樹。
函數 |rotate| 的定義如下：
```haskell
rotate :: RBTree a -> a -> RBTree a -> RBTree a
rotate (R (R s x t) y u) z v  = R (B s x t) y (B u z v)
rotate (R s x (R t y u)) z v  = R (B s x t) y (B u z v)
rotate s x (R (R t y u) z v)  = R (B s x t) y (B u z v)
rotate s x (R t y (R u z v))  = R (B s x t) y (B u z v)
rotate s x t = B s x t {-"~~."-}
```
{.nobreak}其中，前四個情況的左邊分別對應到圖\@ref{fig:red-black-rotate}的四個情況；他們的右手邊都是一樣的，對應到圖\@ref{fig:red-black-rotate}正中央的樹。
最後的 |rotate s x t| 則是四種情況之外、不用旋轉的情形。

### 紅黑樹之性質：高度

許多討論紅黑樹的教材在將插入、刪除等等操作的實作呈現讀者看過之後就結束了，
對於其性質的討論意外地不完整。
然而，這類資料結構之所以有效，正因為它們需有的性質一直被保持著。
談資料結構上的操作卻不證明它們怎麼維護資料結構的性質，可說是缺了最重要的一塊。
本章剩下的篇幅中，我們將描述並證明紅黑樹的一些主要性質。

首先我們談談黑高度。
讀者稍加嘗試之後會發現，|insert k t| 有時會增加 |t| 的黑高度，有時不會。
我們怎知道紅黑樹何時會長高呢？

原來，函數 |ins| 其實是不會讓樹長高的！我們有如下的定理 --- |ins k| 前後樹的黑高度不變：
:::{.theorem #thm:redblack-bheight-ins}
對所有 |k| 與 |t|, |bheight (ins k t) = bheight t|.
:::
{.nobreak}函數 |insert k t| 呼叫 |ins k t|, 得到的樹仍有原來的黑高度。
如果 |blacken| 把樹由紅轉黑，新樹的黑高度才因此加一。
否則樹的黑高度仍不變。
:::{.corollary #thm:redblack-bheight-insert}
對所有 |k| 與 |t|，如果 |ins k t| 為黑色，
|bheight (insert k t) = bheight t|.
否則 |bheight (insert k t) = 1 + bheight t|.
:::

我們將嘗試證明定理\@ref{thm:redblack-bheight-ins}.
回顧我們的原則：*證明的結構依循程式的結構*。
由於 |insert| 呼叫 |ins|, 欲證明關於 |insert| 的系理 \@ref{thm:redblack-bheight-insert}，
我們需要關於 |ins| 的定理 \@ref{thm:redblack-bheight-ins}.
同樣地，由於 |ins| 呼叫 |rotate|, 欲證明定理 \@ref{thm:redblack-bheight-ins},
我們需要一個關於 |rotate| 的引裡：
:::{.lemma #lma:redblack-bheight-rotate}
對所有 |t|, |u| 與 |z|,
|bheight (rotate t z u) = 1 + (bheight t `max` bheight u)|.
:::
這也不意外：|rotate| 的兩個參數 |t| 與 |u| 原本在黑節點之下，旋轉後的黑高度不變，仍是 |1 + (bheight t `max` bheight u)|.

以下我們證明定理\@ref{thm:redblack-bheight-ins}.
:::{.proof}
在 |t| 之上做歸納。以下只列出幾個代表性狀況。

{.nobreak}**狀況** |t := E|.
```spec
   bheight (ins k E)
=  bheight (R E k E)
=  0
=  bheight E {-"~~."-}
```

{.nobreak}**狀況** |t := R t x u|, |k <  x|:
```spec
   bheight (ins k (R t x u))
=    {- |ins| 之定義；|k < x| -}
   bheight (R (ins k t) x u)
=    {- |bheight| 之定義 -}
   bheight (ins k t) `max` bheight u
=    {- 歸納假設 -}
   bheight t `max` bheight u
=    {- |bheight| 之定義 -}
   bheight (R t x u) {-"~~."-}
```

{.nobreak}**狀況** |t := B t x u|, |k <  x|:
```spec
   bheight (ins k (B t x u))
=    {- |ins| 之定義；|k < x| -}
   bheight (balance (ins k t) x u)
=    {- 引理 \ref{lma:redblack-bheight-rotate} -}
   1 + (bheight (ins k t) `max` bheight u)
=    {- 歸納假設 -}
   1 + (bheight t `max` bheight u)
=    {- |bheight| 之定義 -}
   bheight (B t x u) {-"~~."-}
```
:::

為求完整，我們也簡述引理\@ref{lma:redblack-bheight-rotate}之證明：
:::{.proof}
由於 |rotate| 沒有遞迴、不呼叫其他函數，但有許多狀況，
關於 |rotate| 的證明也大都僅是檢查每個情況，雖不難但可能很繁瑣。
以下只舉一種狀況為例。

{.nobreak}**狀況** |(t,z,u) := (R (R t x u) y v, z, w)|:
```spec
   bheight (rotate (R (R t x u) y v) z w)
=    {- |rotate| 之定義 -}
   bheight (R (B t x u) y (B v z w))
=    {- |bheight| 之定義 -}
   (1+ (bheight t `max` bheight u)) `max` (1+ (bheight v `max` bheight w))
=    {- 由於 |(k+x) `max` (k+y) = k + (x `max` y)|, |max| 有結合律 -}
   1 + (((bheight t `max` bheight u) `max` bheight v) `max` bheight w)
=    {- |bheight| 之定義 -}
   1 + (bheight ((R (R t x u) y v)) `max` bheight w)
```
:::

### 紅黑樹之性質：平衡

之所以討論黑高度，目的之一當然是要討論平衡。我們可證明函數 |ins k| 維持平衡性：

:::{.theorem #thm:red-black-balanced-ins}
對所有 |k| 與 |t|, |balanced t ==> balanced (ins k t)|.
:::

{.nobreak}而由於 |balanced t ==> balanced (blacken t)|, 定理 \@ref{thm:red-black-balanced-ins} 蘊含 |insert k| 也維持輸入樹的平衡： |balanced t ==> balanced (insert k t)|.

同樣地，要證明定理 \@ref{thm:red-black-balanced-ins}，我們也需要一個關於 |rotate| 的引理：
:::{.lemma #lma:red-black-balanced-rotate}
對所有 |t| 與 |u|,
```spec
balanced t && balanced u &&
   bheight t = bheight u ==> balanced (rotate t x u) {-"~~."-}
```
:::
{.nobreak}由於這些證明與前面提到的證明類似，我們將它們留給讀者做練習。

:::{.exlist}
:::{.exer}
證明定理\@ref{thm:red-black-balanced-ins}.
你將用得上引理\@ref{lma:red-black-balanced-rotate}與定理 \@ref{thm:redblack-bheight-ins}.
:::
:::{.exans}
在 |t| 之上做歸納。基底情況 |t := E| 很容易建立。
以下只示範一種歸納情況。

{.nobreak}**狀況** |t := B t x u|, |k < x|:
```spec
   balanced (ins k (B t x u))
=    {- |ins| 之定義；|k < x| -}
   balanced (rotate (ins k t) x u)
<==  {- 引理 \ref{lma:red-black-balanced-rotate} -}
   balanced (ins k t) && balanced u && bheight (ins k t) = bheight u
=    {- 定理 \ref{thm:redblack-bheight-ins} -}
   balanced (ins k t) && balanced u && bheight t = bheight u
<==  {- 歸納假設 -}
   balanced t && balanced u && bheight t = bheight u
=    {- |balanced| 之定義 -}
   balanced (B t x u) {-"~~."-}
```spec
:::
:::{.exer}
證明引理\@ref{lma:red-black-balanced-rotate}.
:::
:::{.exans}
以下只示範其中一種狀況。

{.nobreak}**狀況**: |(t,x,u) := (R (R t x u) y v, z, w)|.
```spec
  balanced (rotate (R (R t x u) y v) z w)
=    {- |rotate| 之定義 -}
  balanced (R (B t x u) y (B v z w))
=    {- |balanced| 之定義 -}
  bheight (B t x u) = bheight (B v z w) &&
  balanced (B t x u) && balanced (B v z w)
=    {- |bheight| 之定義 -}
  1 + (bheight t `max` bheight u) = 1+ (bheight v `max` beight w) &&
  bheight t = bheight u && balanced t && balanced u &&
  bheight v = bheight w && balanced v && balanced w
<==  {- |balanced| 與 |bheight| 之定義；算數性質 -}
  bheight (R t x u) = bheight v &&
  balanced (R t x u) && balanced v && balanced w &&
  bheight t `max` bheight u `max` bheight v = bheight w
=    {- |balanced| 與 |bheight| 之定義 -}
  balanced (R (R t x u) y v) && balanced w &&
   bheight R (R t x u) y v = bheight w {-"~~."-}
```
:::
:::

### 紅黑樹之性質：顏色

最後，我們談談紅黑樹插入之後的顏色。我們也許希望函數 |ins k| 能保持準紅黑性，意即 |semiRB t ==> semiRB (ins k t)|.
但這顯然不成立：我們已經知道 |ins k| 可能在一個路徑上產生連續兩個紅節點。

為描述此時的特殊狀況，我們另外定義一個性質：滿足下列述語的樹被稱作*紅外(infrared)樹* --- 取自比紅色還紅一點之意：
```haskell
infrared :: RBTree -> Bool
infrared (R t x u)  =  (color t == Blk || color u == Blk) &&
                         semiRB t && semiRB u
infrared t          =  False {-"~~."-}
```
{.nobreak}紅外樹幾乎是一棵根部為紅色的準紅黑樹，但兩個子樹 |t| 與 |u| 之中最多有一個可以是紅色！我們將其表示成 |color t == Blk || color u == Blk|. 此外，|t| 與 |u| 仍必須是準紅黑樹。其他的情形（|E| 或是 |B _ _ _|）是黑色的，都不是紅外樹。

那麼，我們是否能證明：給定 |ins k| 準紅黑樹 |t|， |ins k t| 總是一個紅外樹，意即 |semiRB t ==> infrared (ins k t)|？
對歸納證明熟悉的讀者可能立刻覺得事有蹊蹺：有二就有三，證明歸納狀況時，如果歸納假設中的子樹有兩個連續的紅節點，在歸納狀況中可能看到三個連續紅節點。如此一來似乎沒完沒了。

這是一個必須嘗試證明一個更強的性質才能使歸納證明成立的例子。
函數 |ins| 真正滿足的是一個更強的性質：
給定準紅黑樹 |t|,
如果 |t| 是紅色，|ins k t| 則是一棵紅外樹；如果 |t| 是黑色，|ins k t| 也將是一棵準紅黑樹：
:::{.theorem #thm:red-black-semiRB-ins}
對所有 |t|:

  1. |semiRB t && color t = Red ==> infrared (ins k t)|,
  2. |semiRB t && color t = Blk ==> semiRB (ins k t)|.



:::
{.nobreak}為證明定理\@ref{thm:red-black-semiRB-ins}，我們也需要一個與 |rotate| 相關的引理：
只要 |t| 與 |u| 之中有一個是準紅黑樹，另一個是準紅黑樹或紅外樹，|rotate t x u| 就會是準紅黑樹：
:::{.lemma #lma:red-black-semiRB-rotate}
對所有 |t| 與 |u|,

  1. |(infrared t |||| semiRB t) && semiRB u ==> semiRB (rotate t x u)|;
  2. |semiRB t && (infrared u |||| semiRB u) ==> semiRB (rotate t x u)|.




:::
{.nobreak}有了定理\@ref{thm:red-black-semiRB-ins}，由於 |infrared t ==> semiRB (blacken t)|，
我們立刻得知 |insert k| 保持準紅黑性：
:::{.corollary}
|semiRB t ==> semiRB (insert k t)|.
:::


以下證明定理\@ref{thm:red-black-semiRB-ins}:
:::{.proof}
定理\@ref{thm:red-black-semiRB-ins}的 1, 2 兩個小性質需在同一個歸納中證明。
注意： 1 與 2 的合取蘊含了
```{.equation #eq:red-black-semiRB-ins-infrared}
|semiRB t ==> (infrared (ins k t) |||| semiRB (ins k t))| \mbox{~~.}
```
{.nobreak}我們將用到此性質。

在 |t| 之上做歸納。我們只舉出兩個具代表性的例子：

{.nobreak}**狀況**: |t := B t x u|, |k < x|:
```spec
   semiRB (ins k (B t x u))
=    {- |ins| 之定義, |k < x| -}
   semiRB (rotate (ins k t) x u)
<==  {- 引理 \ref{lma:red-black-semiRB-rotate} -}
   (infrared (ins k t) || semiRB (ins k t)) && semiRB u
<==  {- 歸納假設，\eqref{eq:red-black-semiRB-ins-infrared} -}
   semiRB t && semiRB u
=    {- |semiRB| 之定義 -}
   semiRB (B t x u) {-"~~."-}
```

{.nobreak}**狀況**:  |t := R t x u|, |k < x|:
```spec
   infrared (ins k (R t x u))
=    {- |ins| 之定義 -}
   infrared (R (ins k t) x u)
=    {- |infrared| 之定義 -}
   (color (ins k t) = Blk || color u = Blk) && semiRB (ins k t) && semiRB u
=    {- 歸納假設 -}
   (color (ins k t) = Blk || color u = Blk) && semiRB t && color t = Blk && semiRB u
<==  {- 命題邏輯: |((P |||| Q) && R) <== (Q && R)| -}
   color t = color u = Blk && semiRB t && semiRB u
=   {- |semiRB| 之定義 -}
   semiRB (R t x u) {-"~~."-}
```
:::

:::{.exlist}
:::{.exer}
證明引理 \@ref{lma:red-black-semiRB-rotate}.
:::
:::{.exans}
本證明只是一一檢查每個狀況。
以 1. |(infrared t |||| semiRB t) && semiRB u ==> semiRB (rotate t x u)| 為例，由於有 |semiRB u|, 我們只需檢查 |rotate| 的第一、第二、與最後一個狀況。
以第一個狀況為例：

{.nobreak}**狀況**: |(t,x,u) := (R (R t x u) y v, z, w)|:
```spec
   semiRB (rotate (R (R t x u) y v) z w)
=    {- |rotate| 之定義 -}
   semiRB (R (B t x u) y (B v z w))
=    {- |semiRB| 與 |color| 之定義 -}
   color t = color u = color v = color w = Blk &&
   semiRB t && semiRB u && semiRB v && semiRB w
=    {- |semiRB| 之定義 -}
   color v = color w = Blk &&
   semiRB (R t x u) && semiRB v && semiRB w
=    {- |infrared| 之定義 -}
   infrared (R (R t x u) y v) && semiRB w
=    {- 命題邏輯，|semiRB (R (R t x u) y v) = False| -}
   (infrared (R (R t x u) y v) || semiRB (R (R t x u) y v)) && semiRB w  {-"~~."-}

```
:::
:::
