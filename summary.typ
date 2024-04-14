// #show math.equation.where(block: true): set align(left)

Это примерный список аксиом, так как некоторые более мощные, чем требуется, и
некоторые сократимы.

Если не сказано иное, то высказывание является определением.

Переменные обозначаются одной буквой.

Mono шрифт обозначает wff переменные.

Serif шрифт английский алфавит обозначают setvar переменные.

Serif шрифт греческий алфавит обозначают class переменные.

По умолчанию setvar переменные принадлежат disjs group.

Если setvar переменная только по одну сторону от $<->$ (возможно,
скрытый), то она образует disj по умолчанию с class переменной с двух сторон.

По предикатам: "$forall x, y space x = y$", "$forall x > 0 space mono(A)$",
"$forall x, y = z space z tilde y$", "$forall w, z = y, i, j, x = z$".

Префиксное связывает сильнее инфиксного.

Предикаты действуют до самого конца, пока не встретят скобку.

= Теория множеств
$ x : "class" $
$
  [y \/ x]mono(A) <->
  forall z = y, x = z space mono(A) | "d:" {x, z}, {y, z}, {z, mono(A)}
$
$ x in {y | mono(A)} <-> [x \/ y] mono(A) $
$ alpha = beta <-> (forall x in alpha <-> x in beta) $
$ alpha in beta <-> (exists x = alpha space x in beta) $
$ {x in alpha | mono(A)} <-> {x mid(|) cases(x in alpha, mono(A))} $
$ (exists x in alpha) -> @alpha in alpha $

Аксиома выделения
$ exists x = {y in z mid(|) mono(A)} $

Аксиома равенства
$ (forall z in x <-> z in y) -> x = y $

$ " " : "list" $
$ alpha L : "at_least_one" | L : "list" $
$ , S : "list" | S : "at_least_one" $
$ {S} : "class" | S : "at_least_one" $
$ alpha in {beta} <-> alpha = beta $
$
  lr(
    alpha in {beta, S} <-> cases(delim: "[", alpha = beta, alpha in {S}) space|
  ) space
  S : "at_least_one"
$

Аксиома пары
$ exists x = {y, z} $

Соглашение: по умолчанию скобки у операция групируются направо, а предикаты
разбиваются на части и формируют конъюнкцию.

$ union alpha = {x | exists y space x in y in alpha} $

Аксиома объединения
$ exists x = union y $

$ alpha subset beta <-> forall x in alpha space x in beta $
$ cal(P) alpha = {x | x subset alpha} $

Аксиома степени
$ exists x = cal(P) x $

$ emptyset = {x | bot} $
$ alpha - "индуктивное" <-> cases(emptyset in alpha, forall y union {y} in alpha) $

Аксиома бесконечности
$ exists x - "индуктивное" $

$ VV = {x | top} $
$ alpha union beta = union {alpha, beta} $
$ sect alpha = {x | forall z space x in z in alpha} $
$ alpha sect beta = sect {alpha, beta} $
$ alpha without beta = {x in alpha | x in.not beta} $
$ alpha triangle.stroked.t beta = (alpha without beta) union (beta without alpha) $
$ (alpha, beta) = {{alpha}, {alpha, beta}} $
$ {(x, y) | mono(A)} = {z mid(|) exists x, y cases(z = (x, y), mono(A))} $
$ {(x, y) in alpha | mono(A)} = {(x, y) mid(|) cases((x, y) in alpha, mono(A))} $
$ alpha times beta = {(x, y) mid(|) cases(x in alpha, y in beta)} $
$ alpha - "бинарное отношение" <-> alpha subset VV times VV $
$ "dom" alpha = {x | exists y space (x, y) in alpha} $
$ "rng" alpha = {y | exists x space (x, y) in alpha} $
$ "back" alpha = {(y, x) | (x, y) in alpha} $
$ alpha compose beta = {(x, y) mid(|) exists z cases((x, z) in beta, (z, y) in alpha)} $
$ alpha harpoon.tr beta = {(x, y) in alpha | x in beta} $
$ alpha harpoon.tl beta = {(x, y) in alpha | y in beta} $
$ alpha arrow.t beta = (alpha harpoon.tl beta) harpoon.tr beta $
$ (alpha, beta) in gamma <-> alpha gamma beta $
$
  alpha - "функциональное" <->
  cases(
    alpha - "бинарное отношение",
    forall x\, y\, z space x alpha y -> x alpha z -> y = z,
  )
$
$
  alpha - "инъективное" <->
  cases(
    alpha - "бинарное отношение",
    forall x\, y\, z space x alpha y -> z alpha y -> x = z,
  )
$
$
  alpha - "функция из" beta <->
  cases(
    exists y space alpha subset beta times y,
    beta subset "dom" alpha,
    alpha - "функциональное",
  )
$
$ alpha_beta = union {y | beta alpha y} $
$ alpha^beta = {x in cal(P)(beta times alpha) | x - "функция из" beta} $
$ x in alpha |-> beta = {(x, y) space mid(|) space cases(x in alpha, y = beta)} $
$
  product alpha =
  {x in (union "rng" alpha)^("dom" alpha) | forall y in "dom" alpha space x_y in alpha_y}
$
$ product.co alpha = {(x, y) | y in alpha_x} $
$
  alpha - "инъекция из" beta <-> cases(alpha - "функция из" beta, alpha - "инъективное")
$
$
  alpha - "сюръекция из" beta space "в" space gamma <->
  cases(alpha - "функция из" beta, gamma subset "rng" alpha)
$
$
  alpha - "биекция из" beta space "в" space gamma <->
  cases(
    alpha - "инъекция из" beta,
    alpha - "сюръекция из" beta space "в" space gamma,
  )
$
$
  alpha lt.curly beta <->
  exists x cases(x subset alpha times beta, x - "инъекция из" alpha)
$
$ alpha tilde beta <-> exists x - "биекция из" alpha space "в" space beta $

Теорема Кантора-Бернштейна-Шрёдера
$ x lt.tilde y -> y lt.tilde x -> x tilde y $

$ x lt.tilde y <-> exists z subset y space x tilde z $
$
  alpha - "рефлексивное" <->
  cases(alpha - "бинарное отношение", forall x in "dom" alpha space x alpha x)
$
$
  alpha - "иррефлексивное" <->
  cases(alpha - "бинарное отношение", forall x cancel(alpha) x)
$
$
  alpha - "симметричное" <->
  cases(
    alpha - "бинарное отношение",
    forall x\, y space x alpha y -> y alpha x,
  )
$
$
  alpha - "антисимметричное" <->
  cases(
    alpha - "бинарное отношение",
    forall x\, y space x alpha y -> y alpha x -> x = y,
  )
$
$
  alpha - "транзитивное" <->
  cases(
    alpha - "бинарное отношение",
    forall x\, y\, z space x alpha y -> y alpha z -> x alpha z,
  )
$
$
  alpha - beta"-минимальный" <->
  cases(
    alpha - "иррефлексивное",
    forall x in "dom" beta space x cancel(beta) alpha,
  )
$
$
  alpha - beta"-максимальный" <->
  cases(
    alpha - "иррефлексивное",
    forall x in "rng" beta space alpha cancel(beta) x,
  )
$
$ alpha - "предпорядок" <-> cases(alpha - "рефлексивное", alpha - "транзитивное") $
$ alpha - "строгий порядок" <-> cases(alpha - "иррефлексивное", alpha - "транзитивное") $
$ alpha - "порядок" <-> cases(alpha - "предпорядок", alpha - "антисимметричное") $
$ "strict" alpha = alpha without {(x, y) in alpha | x = y} $
$
  alpha - beta"-нижняя грань" gamma <->
  cases(beta - "порядок", forall x in gamma space alpha beta x)
$
$
  alpha - beta"-верхняя грань" gamma <->
  cases(beta - "порядок", forall x in gamma space x beta alpha)
$
$ alpha - beta"-наименьший" <-> alpha - beta"-нижняя грань" "dom" beta $
$ alpha - beta"-наибольший" <-> alpha - beta"-верхняя грань" "dom" beta $
$
  alpha - beta"-инфимум" gamma <->
  alpha - beta arrow.t {x | x - beta"-нижняя грань" gamma}"-наибольший"
$
$
  alpha - beta"-супремум" gamma <->
  alpha - beta arrow.t {x | x - beta"-верхняя грань" gamma}"-наименьший"
$
$
  alpha - "решётка" <->
  forall x, y in "dom" alpha
  cases(exists z - alpha"-инфимум" {x, y}, exists z - alpha"-супремум" {x, y})
$
$
  alpha - "полная решётка" <->
  forall x subset "dom" alpha
  cases(exists z - alpha"-инфимум" x, exists z - alpha"-супремум" x)
$
$
  alpha - beta"-цепь" <->
  cases(
    beta - "порядок",
    forall x\, y in alpha cases(delim: "[", x beta y, y beta x),
  )
$
$
  alpha - beta"-антицепь" <->
  cases(
    alpha - "порядок",
    forall x in alpha space x - "strict" (beta arrow.t alpha)"-минимальный",
  )
$
$ alpha - "линейное" <-> "dom" alpha - alpha"-цепь" $
$
  alpha - "фундированное" <->
  cases(
    alpha - "порядок",
    forall x subset "dom" alpha space
      x != emptyset ->
      exists y in x space "strict" y - (alpha arrow.t x)"-минимальный",
  )
$
$ alpha - "полное" <-> cases(alpha - "линейное", alpha - "фундированное") $

Принцип трансфинитной индукции
$
  x - "полное" ->
  (forall y space (forall z != y space z x y -> z in w) -> y in w) -> "dom" x = w $
Есть более мощная форма, но я пока к ней не готов.

Теорема Цермело
$ exists x - "полное" space y = "dom" x $

$ NN = {x | forall y - "индуктивное" space x in y} $
$ alpha - "эквивалентность" <-> cases(alpha - "предпорядок", alpha - "симметричное") $
$ "eq_class" alpha space beta = {x | x alpha beta} $
$ alpha/beta = {x in cal(P) alpha | exists y in alpha space x = "eq_class" beta space y} $

= Алгебра
$
  alpha - "согласованое с" beta <->
  cases(
    alpha - "эквивалентность",
    beta - "операция",
    forall x\, y\, z\, w space x alpha y -> z alpha w -> x beta z alpha y beta w,
  )
$
$
  "Struct"(gamma, alpha, beta) <->
  cases(
    exists x space alpha - "функция из" x,
    forall x in "rng" alpha space exists y space x subset gamma^y,
    exists x space beta - "функция из" x,
    forall x in "rng" beta space exists w space x in gamma^(gamma^w)
  )
$
$
  "Substruct"(gamma, alpha, beta; zeta, delta, epsilon) <->
  cases(
    "Struct"(gamma, alpha, beta),
    "Struct"(zeta, delta, epsilon),
    gamma subset zeta,
    alpha = x in "dom" delta |-> {y in delta_x | "rng" y subset gamma},
    beta =
      x in "dom" epsilon |->
      epsilon_x harpoon.tr {y in "dom" epsilon_x | "rng" y subset gamma},
  )
$
$
  (delta, beta, gamma) lt.tilde^alpha (eta, epsilon, zeta) <->
  cases(
    "Struct"(gamma, alpha, beta),
    "Struct"(zeta, delta, epsilon),
    alpha in eta^delta,
    forall x in "dom" beta\, y in beta_x space alpha compose y in epsilon_x,
    forall x in "dom" gamma\, (y, z) in gamma_x space
      (alpha compose y, alpha_z) in zeta_x,
  )
$
$
  (delta, beta, gamma) tilde.eq^alpha (eta, epsilon, zeta) <->
  cases(
    (delta, beta, gamma) lt.tilde^alpha (eta, epsilon, zeta),
    (eta, epsilon, zeta) lt.tilde^("back" alpha) (delta, beta, gamma),
  )
$
$ (alpha, beta, gamma) = ((alpha, beta), gamma) $
$
  alpha - "операция" <->
  cases(
    alpha subset (beta times beta) times beta,
    "dom" "dom" alpha = "rng" "dom" alpha = "rng" alpha
    )
$
$ alpha beta gamma = beta_((alpha, beta)) $
$
  alpha - "ассоциативное" <->
  forall x, y, z in "rng" alpha space x alpha y alpha z = (x alpha y) alpha z
$
$ alpha - "коммутативное" <-> forall x, y in "rng" alpha space x alpha y = y alpha x $
$
  alpha - "полугруппа" <->
  cases(
    alpha - "операция",
    alpha - "ассоциативное",
  )
$
$
  alpha - "моноид" <->
  cases(
    alpha - "полугруппа",
    exists x in "rng" alpha space forall y in "rng" alpha space
      x alpha y = y alpha x = y,
  )
$
$
  "neut" alpha =
  union{x in "rng" alpha | forall y in "rng" alpha space x alpha y = y alpha x = y}
$
$ 
  alpha - "группа" <->
  cases(
    alpha - "моноид",
    forall x in "rng" alpha space exists y space x alpha y = "neut" alpha,
  )
$
$ "inv" alpha space beta = union{x in "rng" alpha | beta alpha x = "neut" alpha} $
$ 
  alpha - "абелево" <->
  cases(
    alpha - "группа",
    alpha - "коммутативное",
  )
$
$
  (alpha, beta) - "кольцо" <->
  cases(
    alpha - "абелево",
    beta - "полугруппа",
    "rng" alpha = "rng" beta,
    forall x\, y\, z in "rng" alpha space
      x beta (y alpha z) = (x beta y) alpha (x beta z),
    forall x\, y\, z in "rng" alpha space
      (x alpha y) beta z = (x beta z) alpha (y beta z),
  )
$
$ (x, y) - "кольцо" -> ("neut" x = "neut" y <-> "rng" x = {"neut" x}) $
$
  (alpha, beta) - "поле" <->
  cases(
    (alpha, beta) - "кольцо",
    beta - "моноид",
    beta - "коммутативное",
    forall x in "rng" alpha space
      x != "neut" alpha -> exists y space x beta y = "neut" beta,
    "rng" alpha != {"neut" alpha},
  )
$
$ (x, y) - "поле" -> z y w = "neut" x -> cases(delim: "[", z = "neut" x, w = "neut" x) $
$
  (x, y) - "кольцо" ->
  (
    forall z, w space z y w = "neut" x -> cases(delim: "[", z = "neut" x, w = "neut" x)
  ) ->
  z w = i w ->
  w != "neut" x ->
  z = i
$
$ (a + b i)(a - b i) = a^2 + b^2 $
$ (a + b i)^(-1) = (a - b i)/(a^2 + b^2) $
$ |a + b i| = sqrt(a^2 + b^2) $

Поле комплексных чисел $CC$:
- $RR subset CC$
- $i in CC: i^2 = -1$
- оно минимально

Поле комплексных чисел существует и единственно с точностью до изоморфизма.

Класс эквивалентности сравномости по модулю $n$, содержащий целое число a, называется
вычетом числа $a$ по модулю $n$ и обозначается $[a]_n$.

Фактормножество множества $ZZ$ по отношению сравнимости по модулю $n$ обозначается через
$ZZ_n$.
$ ZZ_n = {[0]_n, [1]_n, ..., [n - 1]_n} $

$ZZ_n$ - коммутативное ассоциативное кольцо с единицей. Оно назывется кольцом вычетов по
модулю $n$.

$ ZZ_n - "поле" <-> n - "простое" $
$ [k]_n "обратим в" ZZ_n <-> (n, k) = 1 $

В полях вычетов встречается новое явление, не имевшее место в числовых полях (подполях
комплексных чисел): в поле $ZZ_n$ выполняется $underbrace(1 + 1 + ... + 1, n) = 0$.
Наименьшее $n$, для которого это выполняется, называется характеристикой поля и
обозначается $"char" F$. Если такого $n$ не существует, то $"char" F = 0 $. Таким образом
характеристика числовых полей нулевая.

$ underbrace(x + x + ... + x, "char" F) = (underbrace(1 + 1 + ... + 1, "char F"))x = 0 $
$ (a + b)^("char" F) = a^("char" F) + b^("char" F) $

Малая теорема Ферма: в поле $ZZ_p$ $x^p = x$.

= Логика

Пропозициональные формулы:
- Всякая пропозициональная переменная есть формула.
- Если $A$ - пропозициональная формула, то $not A$ - пропозициональная формула.
- Если $A$ и $B$ - пропозициональные формулы, то $(A and B), (A or B), (A -> B)$ -
  пропозициональные формулы.

Пропозициональная формула задаёт булеву функцию от $n$ переменных.

Пропозициональные формулы, истинные независимо от переменных, называются тавтологиями.

Две формулы эквивалентны $<->$ они задают одну и ту же булеву функцию.

Формулы $mono(x)$ и $mono(y)$ эквивалентны $<->$ $((mono(x) -> mono(y)) and (mono(y) ->
mono(x)))$ - тавтология. Введём сокращения для этой тавтологии $(mono(x) <-> mono(y))$.

Пропозициональные формулы однозначны для разбора.

Теорема о полноте системы связок: любая булева функция может быть задана
пропозициональной формулой.

Литералом называется переменная или отрицание переменной. Конъюнктом называется
произвольная конъюнкция литералов. Дизъюнктивной нормальной формой называется
дизъюнкция конъюнктов. Другая форма - это конъюнктивная нормальная форма.

Всякая булева функция задаётся дизъюнктивной нормальной формой. То же самое про
конъюнктивную нормальную форму.

Система связок $and, not$ является полной. $and, or, ->$ неполна.

Всякая булева функция однозначно представляется полиномом над полем вычетов по модулю 2
с многими переменными - полиномом Жегалкина.

Критерий Поста: Набор булевых функций является полным $<->$ он не содержится целиком
ни в одном из пяти следующих "предполных классов":
- монотонные функции
- функции, сохраняющие нуль ($f(0, ..., 0) = 0$)
- функции, сохраняющие единицу
- линейные функции
- самодвойственные функции ($f(1 - p_1, ..., 1 - p_n) = 1 - f(p_1, ..., p_n)$)

Аксиомы (cхемы аксиом) ичисления высказываний (вообще скобки были, согласно индуктивному
определению, но я их опустил):
+ $A -> B -> A$
+ $(A -> B -> C) -> (A -> B) -> A -> C$
+ $A and B -> A$
+ $A and B -> B$
+ $A -> B -> (A and B)$
+ $A -> (A or B)$
+ $B -> (A or B)$
+ $(A -> C) -> (B -> C) -> (A or B) -> C$
+ $not A -> A -> B$
+ $(A -> B) -> (A -> not B) -> not A$
+ $A or not A$
Тут переменные - это "шаблонные" переменные, в которые подставляются пропозициональные
формулы. В Шень различают эти переменные и пропозициональные переменные.

В исчисление высказываний входит ещё modus ponens: $[A; A -> B] => B$

Вывод в исчислении высказываний - это конечная последовательность формул, каждая из
которых есть аксиома или получается из предыдущих по правилу mp.

Пропощициональная формула называется выводимой в исчислении высказываний или теоремой
исчисления высказываний, если существует вывод, в котором эта формула встречается.

Теорема о корректности ИВ: всякая теорема исчисления высказываний есть тавтология.

Теорема о полноте ИВ: всякая тавтология есть теорема ичисления высказываний.

Вывод из $Gamma$ называется конечная последовательность формул, каждая из которых
является аксиомой, принаждлежит $Gamma$ или получается из предыдущих по правилу mp.
Другими словами, мы как бы добавляем формулы из $Gamma$ к аксиомам исчисления
высказываний - именно как формулы, а не как схемы аксиом. $Gamma = emptyset ->$
формула выводима в ИВ. $A tack.r Gamma$. Вместо $emptyset tack.r A$ пишут $tack.r A$.
$Gamma union {A}$ обозначается $Gamma, A$

Теорема о дедукции: $Gamma tack.r A -> B$ тогда и только тогда, когда $Gamma union {A}
tack.r B$.
