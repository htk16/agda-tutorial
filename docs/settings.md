# Ubuntu 16.04 に Agda をインストールする

Ubuntu 16.04 上に Agda と、推奨開発環境の Emacs をインストールします。
なお Emacs の設定を簡単に済ませるために [Spacemacs](https://github.com/syl20bnr/spacemacs) を使用します。
Spacemacs を使用しない場合は [Agda 2 Readme](https://github.com/agda/agda#configuring-the-emacs-mode) にしたがって設定を行ってください。

## The Haskell tool stack

[公式ドキュメント](https://docs.haskellstack.org/en/stable/README/) の手順にしたがって stack をインストールします。

```sh
curl -sSL https://get.haskellstack.org/ | sh
stack update
stack setup
stack install ghc-mod
stack install apply-refact hlint stylish-haskell hoogle
```

## Agda

stack を使って、Adga 本体と必要なライブラリをインストールします。

```sh
sudo apt-get install libtinfo-dev
stack install Agda
stack install alex happy cpphs
```

2017/03/01 の時点では Agda version 2.5.2 がインストールされました。

### agda-stdlib

標準ライブラリである agda-stdlib は自前でインストールする必要があります。
[ダウンロードページ](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary) から version 0.13 (agda-stdlib-0.13.tar.gz) をダウンロードして、以下の手順でインストールします。

```sh
cd ~
mkdir -p .agda/lib
cd ~/.agda/lib
mv ~/Downloads/agda-stdlib-0.13.tar.gz .
tar zxfv ~/Downloads/agda-stdlib-0.13.tar.gz
echo "$HOME/.agda/lib/agda-stdlib-0.13/standard-library.agda-lib" > ~/.agda/libraries
```

## Emacs & Spacemacs

```sh
sudo apt-get install emacs
git clone https://github.com/syl20bnr/spacemacs ~/.emacs.d
```

前述の設定を行ったあとに Emacs を起動すると、 Spacemacs の初期設定が行われます。
まず最初に、キーバインドを Emacs のものにするか、 Vim like なものにするか確認されるので、お好みで選択してください。
それ以降の質問に対しては初期選択されている項目を選択しておけば問題ないです。

### Agda layer 

Spacemacs では Emacs Lisp パッケージ群とその設定が configuration layer という単位でまとめられています。
[Agda layer](https://github.com/syl20bnr/spacemacs/tree/master/layers/%2Blang/agda) が用意されているので、これを利用します。
Agda layer を有効にするために、~/.spacemacs の dotspacemacs/layers で定義されている dotspacemacs-configuration-layers へ agda を追加します。

```lisp
(defun dotspacemacs/layers ()
  (setq-default
   dotspacemacs-configuration-layers
   '(
     agda   ;; 追加
     ...
     )
   ))
```

設定後 Emacs を再起動すると、 Adga layer に関連するパッケージがインストールされます。
Layer 設定の詳細は [Spacemacs Documentation](https://github.com/syl20bnr/spacemacs/blob/master/doc/DOCUMENTATION.org#declaring-configuration-layers) を参照してください。
