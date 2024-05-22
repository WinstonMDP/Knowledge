#import "cfg.typ": cfg
#show: cfg

= Исчисление секвенций
Такого рода исчисления изучаются в теории доказательств. Они являются исчислениями
генценовского типа.

Секвенция - это $Gamma tack.r Delta$. Тут $tack.r$ не является знаком вывода из ИВ.

Аксиомы - секцвенции, в левых и правых частях которых встречаются только перменные,
причём некоторая переменная встречается в обеих частях.

Правила вывода:

+ $(Gamma tack.r A, Delta quad Gamma tack.r B, Delta)/(Gamma tack.r A and B, Delta)$

+ $(A, B, Gamma tack.r Delta)/(A and B, Gamma tack.r Delta)$

+ $(Gamma tack.r A, B, Delta)/(Gamma tack.r A or B, Delta)$

+ $(A, Gamma tack.r Delta quad B, Gamma tack.r Delta)/(A or B, Gamma tack.r Delta)$

+ $(Gamma, A tack.r B, Delta)/(Gamma tack.r A -> B, Delta)$

+ $(Gamma tack.r A, Delta quad Gamma tack.r B, Delta)/(A -> B, Gamma tack.r Delta)$

+ $(A, Gamma tack.r Delta)/(Gamma tack.r not A, Delta)$

+ $(Gamma tack.r A, Delta)/(not A, Gamma tack.r Delta)$

Контрпример - это набор значений, при которых левая часть секвенции истинна, а правая
ложна.

Корректность и полнота ИС: секвенция выводима $<=>$ она не имеет контрпримера.

Правило сечения: $(Gamma tack.r Delta, A quad Gamma, A tack.r Delta)/(Gamma tack.r Delta
)$

Правило сечения нарушает важное свойство "подформульности" ИС, хотя сохраняет
корректность и полноту.
