# L-meta-18919 · contrôle du candidat v3 du 26 novembre

Le candidat à 44 portes publié au commit `ba2d233d2167af38dff3b38313bcd05e66caab26` calcule exactement huit des neuf sorties. Pour la case centrale, deux des trois produits utilisent la première colonne de B au lieu de la deuxième. Sur les 262 144 entrées, cela produit 33 792 faux positifs et 33 792 faux négatifs. En prenant les indices à partir de zéro et toutes les autres entrées fausses, A[1,0] et B[0,0] donnent un faux positif. A[1,0] et B[0,1] donnent un faux négatif. Lean 4.36.0 a vérifié ces deux cas sur la transcription du circuit. [Fichier Lean](matrix3-v3-counterexamples.lean)

## Peut-on réparer uniquement la porte de sortie centrale ?

La porte qui produit le fil 46 a 46 fils antérieurs disponibles. Aucune porte suivante ne lit ce fil. Pour chacune des 1 081 paires non ordonnées de fils, répétition autorisée, j’ai testé les 16 tables de vérité binaires. Le meilleur des 17 296 choix se trompe encore sur **61 440 entrées** pour la case centrale. En laissant intacts les 44 éléments du circuit et en autorisant une nouvelle sortie calculée sur deux fils quelconques parmi les 62, le meilleur des 31 248 choix a le même nombre d’erreurs. Les 16 tables incluent des opérations extérieures au modèle de l’unité. Même cet ensemble élargi ne contient aucune réparation exacte de ce type.

Deux calculs exhaustifs indépendants ont donné le même minimum. Le premier dénombre, dans chacune des quatre classes de valeurs des deux fils, les entrées où la réponse attendue vaut zéro ou un, puis additionne les quatre minorités. Le second évalue explicitement les 16 tables. Ces bornes concernent exclusivement ce candidat et ces modifications locales. L’existence d’un autre circuit admissible à 44 portes reste ouverte dans ce travail.

## Reproduction depuis la racine de la branche

```python
from pathlib import Path
import itertools,json
root=Path('research/2026-11-26/circuits')
data=json.loads((root/'experiments/matrix3-rejected-candidate-v3.json').read_text())
bits=262144
v=[int.from_bytes(bytes(sum(((x+j)>>i&1)<<j for j in range(8)) for x in range(0,bits,8)),'little') for i in range(18)]
mask=(1<<bits)-1
for gate in data['gates']:
    p=gate['inputs']; a=v[p[0]]
    if gate['op']=='not':v.append(mask^a)
    elif gate['op']=='or':v.append(a|v[p[1]])
    else:v.append(a&v[p[1]])
target=(v[3]&v[10])|(v[4]&v[13])|(v[5]&v[16])
for n in (46,62):
    best=bits;num=0
    for i,j in itertools.combinations_with_replacement(range(n),2):
        a,b=v[i],v[j];union=a|b; inter=a&b
        outputs=(0,mask^union,b&~a,mask^a,a&~b,mask^b,a^b,mask^inter,inter,mask^(a^b),b,~a&mask|b,a,a|~b&mask,union,mask)
        best=min(best,min((target^o).bit_count() for o in outputs));num+=len(outputs)
    print(n,num,best)
    assert best==61440
```

La référence à 45 portes a également repassé le vérificateur Python sur toutes les entrées. Ce contrôle de recherche n’a donné lieu à aucune soumission d’unité.
