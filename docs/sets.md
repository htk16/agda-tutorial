<!-- Agda tutorial を読んでみた: Sets (1) -->

[Agda Tutorial](http://people.inf.elte.hu/divip/AgdaTutorial/Index.html) を読んで、自分なりにまとめたメモ。

<!--
- [Emacs Usages](http://people.inf.elte.hu/divip/AgdaTutorial/Emacs_Usage.html#1)
- [Adga Emacs Symbols](http://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html#1)
-->

# Modules
すべての Agda module は以下のような形式のヘッダから始まります。

```agda
module Modules.Basic where
```

- module と where は Agda の keyword (予約語)
- モジュール名とファイルシステム上でのファイル名は一致させる必要があります。先の例ではファイル名を Modules/Basic.agda のようにします
- Emacs で Agda module を開いて agda2-load (C-c C-l) を実行すると、正しく読み込めた場合は Syntax Highlight されます

# Enumerated Sets
## The Bool set
```agda
data Bool : Set where
  true  : Bool
  false : Bool
```

上記定義の意味するところは
- Bool の型は Set (任意の集合を要素に持つ集合)
- true, false は Bool の要素でそれぞれ異なる
- true, false 以外には Bool の要素は存在しない
true や false は Bool データ型のコンストラクタ(constructor) と呼ばれます。

Agda では Block 構造をインデントで表します (off-side rule)。
Bool のコンストラクタなどは data ... の行よりも一段深く字下げしてから記述します。
あと、: 前後にはスペースが必要です。
Bool: Set のように省略してしまうと Bool: を1識別子として解釈してしまいます。

## Isomorphisms
```agda
data Bool' : Set where
  true'  : Bool'
  false' : Bool'

data Bool' : Set where
  true'  : Bool'
  false' : Bool'
```

Bool と Bool' は異なるデータ型ですが、
true と true'、false と false' の間に一対一の対応関係があるので同型(isomorphic)です。

## Representation and interpretation
解釈 (interpretation) と表現 (representation)は逆の関係です
- Bool は「真理値(Boolean)の集合」と解釈することができます
- 真理値の集合の一つの表現が Bool です
- 真理値の集合の Bool とは異なる表現の一つが Bool' です

## Special finite sets
Agda では要素数が n = 0, 1, 2, ... の集合を定義することができます。
その中で、 n = 0, 1 の場合の特別な集合に ⊥, ⊤ があります。

```agda
data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤
```

余談ですが ⊥ および ⊤ は input-method を Agda に設定したあと、それぞれ \bot, \top で入力できます。Adga input method で入力できる記号の一覧は [こちら](http://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html#1)

## Types vs. sets
型(types) と集合(sets) には次の基本的な違いがあります。
- 要素の型はユニークだが、要素は異なる集合の要素になることができる (例えば true は同時に2つの異なる型の要素にはなれない)
- 型はその要素のコレクションではないが、集合はその要素によって特徴づけられる (例えば異なる空集合が存在する)
data は型を定義するもので、集合を定義するものではありません。

いくつかの理由から集合より型を好んで使う、とあるのですが自分は今のところその理由は理解できていません。そのうちわかるでしょう、きっと。

# Recursive Sets
## Definition of ℕ

ペアノの公理に基づいて自然数 ℕ を定義します。
```agda
data ℕ : Set where
  zero :      ℕ
  suc  : ℕ → ℕ
```
zero は 0 を、suc は自然数 n の後者(successor)を表すコンストラクタとなります。
suc : ℕ → ℕ は ℕ 型の要素をとって ℕ 型の要素を返すコンストラクタを表しています。

Agda 上の項と数値表現の対応は以下のようになります。

| 項 | 数値表現 |
|----|----------|
| zero | 0 |
| suc zero | 1 |
| suc (suc zero) | 2 |
| suc (suc (suc zero)) | 3 |
| ... | ... |

Emacs の agda2-infer-type-maybe-toplevel (C-c C-d) コマンドを使うと、与えた項の型を確認することができます。

自然数には、以下のような ℕ とは別の表現を考えることもできます。
```agda
data ℕ⁺ : Set where
  one      :      ℕ⁺
  double   : ℕ⁺ → ℕ⁺
  double+1 : ℕ⁺ → ℕ⁺

data ℕ₂ : Set where
  zero :      ℕ₂
  id   : ℕ⁺ → ℕ₂
```
ℕ₂ でもコンストラクタ zero が定義されています。
曖昧にならない場合に限り、同じ名前のコンストラクタを複数の型で定義することができます(どういう場合に曖昧になるんですかね？)。

ℕ と ℕ₂ は同型で、以下のような対応関係があります。

| ℕ | ℕ₂ |
|---|----|
| zero | zero |
| suc zero | id one |
| suc (suc zero) | id (double one) |
| suc (suc (suc zero)) | id (double+1 one) |
| ... | ... |

### Rationale behind different representations
ℕ と ℕ₂ はどちらも自然数を定義する型です。
どちらか一方があれば良いようにも思えますが、使い分けることで扱う問題によっては簡潔な表現ができる場合があります。
例えばある自然数 n に対して n * 2 を計算する場合、 ℕ₂ であれば単に double コンストラクタを使うことで表現できます (実際は ℕ₂ を剥がして ℕ⁺ の値を取り出す必要はありますが)。
一方 ℕ の要素 n に対しては、何らかの手段で ℕ 上の積演算を定義する必要があります。

## Binary trees
節点が値を持たない二分木は以下のように定義できます。
```agda
data BinTree : Set where
  leaf : BinTree
  node : BinTree → BinTree → BinTree
```

TODO 図を入れる

```agda
leaf
node leaf leaf
node (node leaf leaf) leaf
node leaf (node leaf leaf)
node (node leaf leaf) (node leaf leaf)
```

同様に、葉のみが自然数をラベルに持つ二分木は以下のように定義できます。
```agda
data BinTreeℕ : Set where
  leaf : ℕ -> BinTreeℕ
  node : BinTreeℕ -> BinTreeℕ -> BinTreeℕ
```

# Constant Definitions

(定数名) = (式) の形式で定数を定義することができます。
定数の定義の前の行に (定数名) : (型) の形式で定数の型を明示しています。
型は曖昧にならない範囲で省略することができます。

```agda
nine : ℕ
nine = suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))

ten : ℕ
ten = suc nine
```

`ten`, `suc nine`, そして `suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))` は
どれも自然数10を表現しています。
この中で `suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))` のように
コンストラクタだけで表現されたものを **標準形** (normal form) と呼びます。

# Decimal Notation for Natural Numbers

`zero` と `suc` を使った自然数の表現だと、3 あたりから
値がいくつなのか把握するのが難しくなってきます。
かといって毎回値に名前をつけるのも面倒です。
幸いなことに、標準ライブラリで定義されている自然数 ℕ では
値を十進数で表記することができます。

標準ライブラリの Data.Nat モジュールには自然数を表す型 ℕ 、
およびそのコンストラクタ `zero` と `suc` が定義されています。
Data.Nat モジュールから `ℕ, zero, suc` を import することで、
型とコンストラクタを利用できるようになります。

```agda
open import Data.Nat public using (ℕ; zero; suc)

three : ℕ
three = 3

three' : ℕ
three' = suc (suc (suc zero))
```

`3` は `suc (suc (suc zero))` の短縮形となります。
これ以降自然数 ℕ は、自分で定義した自然数ではなく、 Data.Nat モジュールで定義されたものを使用します。

# Infix Notation

ここまでの例では、コンストラクタは前置の演算子として定義されていました。
agda では中置のコンストラクタを定義することも可能です。
もっと言えば後置や3つ以上の項を取る演算子としても定義可能です。

```agda
data BinTree' : Set where
  x : BinTree'
  _+_ : BinTree' → BinTree' → BinTree'
  
infixr 3 _+_
```

`BinTree'` は節点がラベルを持たない二分木を表す型です。
`x` は葉を、 `_+_` は節を表すコンストラクタです。
`_+_` のアンダースコアは `+` の前と後に1つずつ値をとることを表すプレースホルダです。
`infixr 3 _+_` は `+` が右結合で、(結合の優先度が3 (高いほど優先して結合される)) であることを宣言しています。
もし左結合にする場合は `infixr` の代わりに `infixl` を使います。
なお、これまでの例で出てきたアンダースコアを含まないコンストラクタは、前置の演算子として扱われます。

| BinTree | BinTree' |
|---|---|
| leaf | x |
| node leaf leaf | x + x |
| node (node leaf leaf) leaf | |
| node leaf (node leaf leaf) | |
| node (node leaf leaf) (node leaf leaf) | |

# Mutually Recursive Sets

型の定義を行う前に型の宣言を先行して行うことで、相互再帰的な型を定義することができます。

```agda
data L : Set
data M : Set

data L where
  nil : L
  _∷_ : ℕ → M → L

data M where
  _∷_ : Bool → L → M
  
L₁ : L
L₁ = nil 

R₁ : R
R₁ = true ∷ L₁

L₂ : L
L₂ = (suc zero) ∷ R₁
```

ちなみに ∷ は \:: で入力できます。
あと → と -> は等価です。

## Exercise: 各ノードが有限個の子を持つ木を定義せよ

木自体はデータ型 `Tree` で表すとします。
`Tree` のコンストラクタ `node` はある(部分)木の根のノードを表します。
`node` は `Children` データ型で表現される子の列を取ります。
一方 `Children` は `Tree` の要素をもつリストです。
2つのコンストラクタ `nil` と `_,_` を持ち、
その要素は `t1 , t2 , ... , tn , nil` の形式で表されます (`t1` ... `tn` は `Tree` の要素)。

```agda
data Tree : Set
data Children : Set


data Tree where
  node : Children -> Tree

data Children where
  nil : Children
  _,_ : Tree -> Children -> Children

infixr 5 _,_

root : Tree
root = node nil

tree1 : Tree
tree1 = node (node nil , node nil , nil)

tree2 : Tree
tree2 = node (tree1 , node nil , tree1 , nil)
```

# Parametric Sets

## Definition of List

Agda のデータ型はパラメータを取ることができます。
データ型の宣言で、データ型名の後、コロンの前にパラメータを指定できます。

```agda
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_
```

`A` および `List A` は Set の要素で、 `A` は `List A` のパラメータです。
`List A` は `A` 型の要素を持つリストとみなすことができます。
例えば `List Bool` の要素は `true ∷ []` や `false ∷ false ∷ []` などのリストです。
それぞれのリストは `Bool` 型の値を要素としています。

## Cartesian Product 

```agda
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 4 _,_
infixr 2 _×_
```

`A × B` は Set `A` と `B` の直積集合を表します。
`a , b` は `A × B` の要素です (`a` ∈ `A` かつ `b` ∈ `B`)。
例えば `Bool × Bool` の要素は以下の4つになります。

```agda
true , true
true , false
false , true
false , false
```

なお `_×_` が2つのパラメータ `A` と `B` を取ることを
`data _×_ (A B : Set)` の形式で宣言していますが、 
`data _×_ (A : Set) (B : Set)` と等価です。


<!--
## Disjoint Union

```agda
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 1 _⊎_
```
-->

## Mutually recursive sets

もちろん相互再帰で定義される型もパラメータを持つことができます。

```agda
data List₁ (A B : Set) : Set
data List₂ (A B : Set) : Set

data List₁ (A B : Set) where
  []  :                 List₁ A B
  _∷_ : A → List₂ A B → List₁ A B

data List₂ (A B : Set) where
  _∷_ : B → List₁ A B → List₂ A B

```

ちなみに以下のような非正規再帰型 (non-regular recursive type) でも同様に定義することができます。

```agda
data AlterList (A B : Set) : Set  where
  []  :                     AlterList A B
  _∷_ : A → AlterList B A → AlterList A B
```

### Exercise: `List₁ ⊤ Bool` の最も小さい最初の5要素を示せ
「最も小さい」の定義は、構成する項数が最も少ないもの、と解釈。
```agda
[]
true :: tt :: []
false :: tt :: []
true :: tt :: true :: tt :: []
true :: tt :: false :: tt :: []
```

<!--
## Nested set

```agda
data T4 (A : Set) : Set where
  quad : A → A → A → A → T4 A

data Square (A : Set) : Set where
  zero :            A  → Square A   -- 2^0 rows
  suc  : Square (T4 A) → Square A   -- 2^(n+1) rows
```

TODO 説明する
-->

# Indexed Sets

Agda のデータ型は型パラメータを取ることができます。
この型パラメータは値にデータ型だけでなく、

## Fin, family of finite sets

集合 ℕ で添字づけられた集合族 `Fin` を考えます。
ここで `Fin n (n ∈ ℕ)` は `n` 個の要素を持つ集合とします。
例えば `Fin 0, Fin 1, ...` は以下のような集合と同型です。

| `n` | `n` 個の要素を持つ集合 |
|-----|------------------------|
| `0` | `Fin 0 ~ ⊥` |
| `1` | `Fin 1 ~ ⊤ ~ Maybe ⊥ ~ ⊤ ⊎ ⊥` |
| `2`  | `Fin 2 ~ Bool ~ Maybe ⊤ ~ Maybe (Maybe ⊥) ~ ⊤ ⊎ ⊤ ⊎ ⊥ ` |
| `3`  | `Fin 3 ~ Maybe Bool ~ Maybe (Maybe (Maybe ⊥)) ~ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊥ ` |
| `4` |  `Fin 4 ~ Maybe (Maybe (Maybe (Maybe ⊥))) ~ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊤ ⊎ ⊥ ` |
| ...  | ... |

なお、 `Maybe` , `⊤` , `⊥` , `⊎` の定義は以下のとおりです。

```agda
data Maybe (A : Set) : Set where
  none : Maybe A
  some : A -> Maybe A
  
data ⊤ : Set where
  tt : ⊤
  
data ⊥ : Set where

data _⨄_ (A B : Set) : Set where
  inj₁ : A -> A ⨄ B
  inj₂ : B -> A ⨄ B

infixr 1 _⨄_
```

## Definition of Fin

Agda 上で `Fin` を定義してみる。

```agda
data Fin : ℕ → Set where
  zero : (n : ℕ) → Fin (suc n)
  suc  : (n : ℕ) → Fin n → Fin (suc n)
```

(データ型 `Fin` は型パラメータとして `ℕ` 型を1つ取り、 `Set` の要素を返す)
`Fin n` は `n` 個の要素を持つ集合です。

|         |      |
|---------|------|
| `Fin 0` | `{}` |
| `Fin 1` | `{zero 0}` |
| `Fin 2` | `{zero 1, suc 1 (zero 0)}` |
| `Fin 3` | `{zero 2, suc 2 (zero 1), suc 2 (suc 1 (zero 0))}` |
| `Fin 4` | `{zeor 3, suc 3 (zero 2), suc 3 (suc 2 (zero 1)), suc 3 (suc 2 (suc 1 (zero 0)))}` |
| ... | ... |

TODO: 依存型に触れる

### Exercise

TODO: なんか一つ触れる

## Vec A n ~ An

`Vec A n` は A 型の要素をもつ `n` つ組 (n-tuple) です。

```agda
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  cons : (n : ℕ) → A → Vec A n → Vec A (suc n)
```

# Term Inference and Implicit Arguments

# Propositions

# Parametric vs. Indices
