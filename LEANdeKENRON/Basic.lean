
namespace my

namespace CategoryTheory

universe v u

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

/--合成の記号（図式順）-/
scoped infixr:80 " ≫ " => CategoryStruct.comp

/--
ベシ圏などでの合成の書き方。notationを使うことで順番入れ替えができる。
gを
-/
scoped notation g:80 " ⊚ " f:81 => CategoryStruct.comp f g

/--圏の定義（公理）-/
class Category (obj: Type u) : Type max u (v+1) extends CategoryStruct.{v} obj where
  /--左恒等射律-/
  id_comp : ∀ {X Y: obj} (f : X ⟶ Y), 𝟙 X ≫ f = f
  /--右恒等射律-/
  comp_id : ∀ {X Y: obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f

  /--合成の結合律-/
  assoc : ∀ {W X Y Z: obj} (f:W⟶X) (g:X⟶Y) (h:Y⟶Z), (f≫g)≫h = f≫(g≫h)

/-
simp(,grind)にて圏の公理を使えるようにする。
mathlibには
attribute [to_dual existing (attr := simp, grind =) id_comp] Category.comp_id
なる記述があるがto_dualは使えないので保留
-/
attribute [simp, grind _=_] Category.assoc
attribute [simp] Category.comp_id Category.id_comp


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

attribute [simp] Functor.map_id Functor.map_comp

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

def comp (F:C⥤D) (G:D⥤E) : C⥤E where
  obj := G.obj∘F.obj --または fun x↦ G.obj (F.obj x)
  map := G.map∘F.map
  map_id := by simp
  map_comp := by simp



end
end Functor

/--恒等関手の記法：Functorを開かなくてもCategoryTheoryを開けば使える-/
scoped notation "𝟭" => Functor.id
scoped infixr:80 " ⋙ " => Functor.comp

namespace Functor
variable {C:Type u1} [Category.{v1} C] {D:Type u2} [Category.{v2} D] {E:Type u3} [Category.{v3} E]
@[simp]
theorem id_obj (X : C) : (𝟭 C).obj X = X := rfl
@[simp]
theorem id_map {X Y : C} (f : X ⟶ Y) : (𝟭 C).map f = f := rfl
@[simp]
theorem comp_map (F:C⥤D) (G:D⥤E) {X Y:C} (f:X⟶Y) :
  (F⋙G).map f = G.map (F.map f) := rfl

end Functor


end CategoryTheory

end my
