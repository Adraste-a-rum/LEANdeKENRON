
namespace my

namespace CategoryTheory

universe v u

/-宣言コマンド(`class`など)の前に`/--hogehoge-/`と書くとdoc commentとして利用できる-/

/--Quiver(えびら、箙)。圏から合成と恒等射を忘れたもの（有向グラフ？）-/
class Quiver (V : Type u) : Type (max u (v+1)) where
  /--射の型（HomSet）-/
  Hom : V → V → Type v

/-
v+1について：
たとえば頂点が{*}(一点集合)、その頂点からその頂点への辺がすべての集合　であるような箙を考えると、Hom: Type 0 → Type 0 → Type 0 となるが、この箙は「すべての集合の集合」であるからType 1になる
-/

--豆知識：`@[inherit_doc]`で注記を継承できる

/--射の型を表す記号。関数記号`→`とは別物-/
infixr:10 " ⟶ " => Quiver.Hom --スペースを含めておくといろいろ楽（InfoViewで見やすい、書くときはスペース省略可）

/--
圏の構造（数学基礎論的に言えば「言語」）だけ先に定義する
これにより公理を記述するときにnotation(infixで定義するやつ)が使える
-/
class CategoryStruct (obj : Type u ) : Type (max u (v+1)) extends Quiver.{v} obj where
  /--恒等射-/
  id : ∀ X:obj, X ⟶ X

  /--合成-/
  comp : ∀ {X Y Z:obj}, (X⟶Y) → (Y⟶Z) → (X⟶Z)

/--恒等者の記号-/
scoped notation "𝟙" => CategoryStruct.id

/--ベシ圏などでの合成の書き方。notationを使うことで順番入れ替えができる。-/
scoped notation g:80 " ⊚ " f:81 => CategoryStruct.comp f g

/--mathlibなどでの合成の記号（図式順）-/
scoped infixr:80 " ≫ " => CategoryStruct.comp

/- InfoViewでは後に書いた記法が優先されるため、図式順を後に書いている -/

/--圏の定義（公理）-/
class Category (obj: Type u) : Type max u (v+1) extends CategoryStruct.{v} obj where
  /--左恒等射律-/
  id_comp : ∀ {X Y: obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  /--右恒等射律-/
  comp_id : ∀ {X Y: obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f

  /--合成の結合律-/
  assoc : ∀ {W X Y Z: obj} (f:W⟶X) (g:X⟶Y) (h:Y⟶Z), (f≫g)≫h = f≫(g≫h)

/-
`simp`(および`grind`)にて圏の公理を使えるようにする。
mathlibには
attribute [to_dual existing (attr := simp, grind =) id_comp] Category.comp_id
なる記述があるがto_dualは使えないので保留
-/
attribute [simp, grind _=_] Category.assoc
attribute [simp] Category.comp_id Category.id_comp

/- 宇宙変数の宣言 CategoryTheory空間内でつかえる -/
universe v1 v2 v3 u1 u2 u3

/--関手-/
structure Functor (C : Type u1) [Category.{v1} C] (D:Type u2) [Category.{v2} D] :
    Type max v1 v2 u1 u2 where
  /--対象についての関数-/
  obj : C → D
  /--射についての関数 Hom(X,Y) → Hom(F(X),F(Y))-/
  map : ∀ {X Y:C},(X⟶Y) → ((obj X)⟶(obj Y))

  /--恒等射の保存-/
  map_id: ∀ X:C, map (𝟙 X) = 𝟙 (obj X)
  /--合成の保存-/
  map_comp : ∀ {X Y Z:C} (f:X⟶Y) (g:Y⟶Z), map (f≫g) = (map f)≫(map g)

/--関手記号-/
scoped infixr:26 " ⥤ " => Functor

/-恒等射・合成の保存公理を`simp`でつかえるようにする-/
attribute [simp] Functor.map_id Functor.map_comp

/- F -/
namespace Functor

section
variable (C:Type u1) [Category.{v1} C]
/--恒等関手-/
protected def id : C⥤C where
  obj := id
  map := id
  map_id := by simp
  map_comp := by simp
end

section
variable {C:Type u1} [Category.{v1} C] {D:Type u2} [Category.{v2} D] {E:Type u3} [Category.{v3} E]

/--関手の（水平）合成-/
def comp (F:C⥤D) (G:D⥤E) : C⥤E where
  obj := G.obj∘F.obj --または fun x↦ G.obj (F.obj x)
  map := G.map∘F.map
  map_id := by simp
  map_comp := by simp
end

end Functor

/--恒等関手の記法：Functorを開かなくてもCategoryTheoryを開けば使える-/
scoped notation "𝟭" => Functor.id

/--関手の合成の記法：Functorを開かなくてもCategoryTheoryを開けば使える-/
scoped infixr:80 " ⋙ " => Functor.comp

namespace Functor
variable {C:Type u1} [Category.{v1} C] {D:Type u2} [Category.{v2} D] {E:Type u3} [Category.{v3} E]

/--恒等関手の性質：対象について恒等関数-/
@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl

/--恒等関手の性質：射について恒等関数-/
@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl

/-- 合成関手の性質：射についてはFunctor.mapの合成 -/
@[simp]
theorem comp_map (F:C⥤D) (G:D⥤E) {X Y:C} (f:X⟶Y) :
  (F⋙G).map f = G.map (F.map f) := rfl

end Functor

/- ふつう圏論ではC,D,Eは圏なのでそういうふうに変数宣言する -/
variable {C:Type u1} [Category.{v1} C] {D:Type u2} [Category.{v2} D]

/- ここから alg-d.com/math/kan_extension/kan_extension_short.pdf に従うため圏の対象は`a,b,...`というように置く -/

/-- 自然変換(射の族 {θₐ:Fa→Ga} ) -/
structure NatTrans (F G: C ⥤ D): Type max u1 v2 where -- max u1 v2とするのは自然変換の定義(Cの対象とDの射がデータなる)から明らか
  /-- θ.app c でθのc成分を表す -/
  app (c:C) : F.obj c ⟶ G.obj c
  /-- 自然性(θₐ₂∘Ff = Gf∘θₐ₁ ) -/
  naturality ⦃a1 a2:C⦄ (f : a1 ⟶ a2) : F.map f ≫ app a2 = app a1 ≫ G.map f -- `app a2 ≫ F.map f = G.map f ≫ app a1` とすると型エラーが起きるので書き間違えずに済む。LEAN最強！！

-- Mathlibを読むときの方針：to_dualは無視！！

-- この段階ではまだ関手圏を定義できていないため、(θ:F⇒G)のような自然変換を表す記号は導入できない

namespace NatTrans

section
variable {F G H : C ⥤ D}
/-- 自然変換の垂直合成-/
def vcomp (θ:NatTrans F G) (σ : NatTrans G H) : NatTrans F H where
  app : (c : C) → F.obj c ⟶ H.obj c :=
    fun c ↦ θ.app c ≫ σ.app c
  naturality:= by
    intro a1 a2 f
    have:= σ.naturality
    simp
    rw[←this f]
    simp[← @Category.assoc]
    rw[θ.naturality f]
    done
end

--第3回の予定：関手圏、水平合成（、"貼り合わせ"Fθ●σG）の導入（、ペースティング定理の証明）

--第3回

--垂直合成の記号は射の合成の記号を用いるので、さきに関手圏を定義

/--恒等自然変換-/
protected def id (F : C ⥤ D) : NatTrans F F where
  app c := 𝟙 (F.obj c)
  naturality := by simp

end NatTrans


instance Functor.category (C:Type u1) (D:Type u2) [Category.{v1} C] [Category.{v2} D] : Category (C ⥤ D) where
  Hom F G := NatTrans F G
  id F:= NatTrans.id F
  comp θ σ := NatTrans.vcomp θ σ
  id_comp := by simp[NatTrans.id, NatTrans.vcomp]
  comp_id := by simp[NatTrans.id, NatTrans.vcomp]
  assoc :=
    show ∀ {W X Y Z : C ⥤ D}
            (f : NatTrans W X)
            (g : NatTrans X Y)
            (h : NatTrans Y Z),
              (f.vcomp g).vcomp h = f.vcomp (g.vcomp h)
    by simp[NatTrans.vcomp]



end CategoryTheory

end my
