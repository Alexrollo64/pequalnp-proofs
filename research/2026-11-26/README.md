# Recherche pequalnp du 26 novembre 2026

Ce dossier rassemble le travail de recherche effectué pour Alexrollo64 sur les unités du projet pequalnp. Les sources sont publiées sous la licence Apache 2.0 du dépôt. Le dossier contient des programmes, des constructions de référence et des résultats intermédiaires reproductibles.

| Suivi | État à la publication |
| --- | --- |
| Preuves complètes d’unités soumises au projet pendant ces sessions | 0 |
| Preuves acceptées par le vérificateur du projet pendant ces sessions | 0 |
| Fichiers de résultats Lean vérifiés localement | 2 |
| Formules SAT restreintes exclues avec un contrôle DRAT indépendant | 21 |
| Circuits de référence 4 × 5 vérifiés sur leurs vingt entrées | 14 |
| Recherche sur L-meta-21111 | Réservation rendue après essais sans témoin |
| Unité actuellement travaillée | L-meta-18919, tranche 6 sur 16 |

## Encodeur sur seize entrées

L’unité L-meta-19060 demande un circuit monotone d’au plus 31 portes donnant les quatre bits de la position d’une entrée active, ainsi que leurs quatre compléments.

Le fichier Lean donne une formalisation du circuit de référence connu à 32 portes, la valeur de ses huit fils et deux lemmes de comptage. Cette construction dépasse d’une porte la limite demandée. Le problème à 31 portes reste ouvert dans ce travail. [Lire le fichier Lean](encoder/L_meta_19060_progress.lean)

Un programme SAT étudie les circuits dont les supports intermédiaires sont des sous-cubes des quatre bits d’adresse, avec au plus un support distinct supplémentaire. Les premières unions irrégulières possibles forment 21 classes par symétrie. Les 21 formules produites ont donné UNSAT et leurs certificats DRAT ont été contrôlés par drat-trim. La traduction en SAT et la réduction par symétrie sont implémentées en Python. Le fichier Lean porte sur le circuit à 32 portes et le comptage. [Programme et résultats](encoder/encoder-orbits.py) · [Journal des 21 cas](encoder/resultats-21-cas.txt)

Les empreintes SHA-256 des 42 fichiers CNF et DRAT de cette exécution sont publiées pour comparer une régénération. Le contrôle DRAT établit l’insatisfaisabilité de chaque CNF associée. [Empreintes des certificats](encoder/SHA256SUMS.txt)

## Circuits sur des graphes 4 × 5

Chaque unité fixe un masque de vingt bits et une taille maximale. Le circuit reçoit exactement un sommet actif de chaque côté du graphe. Les constructions de référence publiées ont été évaluées sur les vingt entrées permises. Les limites demandées et les tailles obtenues figurent dans le relevé. [Résultats par unité](circuits/results.json)

Trois méthodes sont fournies. Une recherche de formules AND/OR produit les constructions de référence. Une recherche de sous-expressions communes essaie de partager des fils intermédiaires. Une synthèse SAT choisit les opérations et les connexions d’un circuit de taille fixée. Les options `ordered`, `minimal`, `fanout` et `repair_radius` ajoutent des restrictions au modèle de recherche. Un verdict UNSAT doit être interprété avec les paramètres employés. [Recherche de formules](circuits/promise-formula.cpp) · [Recherche avec partage](circuits/shared-search.cpp) · [Synthèse SAT](circuits/synth-circuit.py)

Le fichier L_meta_4131_progress contient également des lemmes auxiliaires sur deux paires d’un graphe. Il a été vérifié localement avec Lean. L’unité complète reste à résoudre. [Lemmes auxiliaires](L_meta_4131_progress.lean)

## Reproduction

Les deux fichiers Lean ont été vérifiés avec Lean 4.36.0 et les dépendances du dépôt au commit `1b129350cb6ba392b73f11af10e914e9ef7c77fd`. Depuis le répertoire `lean` du dépôt, les commandes suivantes reconstruisent les définitions puis vérifient les fichiers.

```sh
lake exe cache get
lake build PEqualNP.Defs
lake env lean ../research/2026-11-26/encoder/L_meta_19060_progress.lean
lake env lean ../research/2026-11-26/L_meta_4131_progress.lean
```

Depuis ce dossier de recherche, le contrôle des quatorze circuits de référence utilise uniquement Python.

```sh
python3 circuits/verify-baselines.py
```

La synthèse SAT utilise python-sat et CaDiCaL 1.9.5. Le fichier d’entrée publié demande dix portes pour L-meta-21111. La commande écrit un circuit si elle trouve un témoin.

```sh
python3 -m venv /tmp/pequalnp-research-env
/tmp/pequalnp-research-env/bin/pip install -r circuits/requirements.txt
/tmp/pequalnp-research-env/bin/python circuits/synth-circuit.py \
  circuits/L-meta-21111-table.json /tmp/L-meta-21111-circuit.txt
```

Pour régénérer et contrôler les 21 certificats, installer drat-trim puis fournir le chemin de son exécutable. L’exécution initiale a utilisé drat-trim au commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`.

```sh
/tmp/pequalnp-research-env/bin/python encoder/encoder-orbits.py \
  --checker /chemin/vers/drat-trim --certdir /tmp/pequalnp-certificats --jobs 3
```

## Soumissions au projet pequalnp

L’attribution des unités utilise le handle GitHub Alexrollo64. Les réservations sont renouvelées pendant le travail. Chaque preuve complète destinée au projet suit la procédure de tools/pnp.sh et les règles de CONTRIBUTING.md.

Une soumission de preuve utilise une branche dédiée, un commit et le fichier Lean nommé par le bureau. L’énoncé est celui de l’unité attribuée. Le titre de la pull request est l’identifiant de l’unité. Son corps contient `Lease: <identifiant de réservation>`. Le crédit est enregistré après ACCEPTED et fusion par le projet. [Instructions du site](https://pequalnp.com/join.txt) · [Règles du dépôt](../../CONTRIBUTING.md)

## Suite de la recherche

Les trois recherches SAT prolongées sur L-meta-21111 ont été interrompues sans verdict. Une seconde traduction SAT a atteint sa limite de 120 secondes sans verdict. Une recherche de deux supports partagés a testé 5 000 configurations. Quatre recherches stochastiques, aux budgets de 8 à 11 portes, ont terminé 320 millions d’itérations au total en prenant en compte les permutations des entrées. Le contrôle positif retrouve le circuit de référence à onze portes. Les essais sont consignés avec leurs paramètres et leurs issues. [Relevé de la session](circuits/experiments/session-2.json)

La recherche actuelle porte sur le produit de deux matrices booléennes 3 × 3. Le bureau a attribué L-meta-18919, tranche 6 sur 16. Cette tranche impose un circuit d’au plus 44 portes, exactement une porte NON et de 23 à 33 portes ET. Les neuf sorties sont celles du produit booléen. Le programme cherche sur 512 entrées d’essai et contrôle tout candidat qui passe ces essais sur les 262 144 entrées possibles. La référence connue à 45 portes a passé ce contrôle complet. La tranche reste en cours de recherche. [Données de l’attribution](circuits/active-search.json) · [Programme de recherche](circuits/matrix3-search.cpp)

Les commandes suivantes, exécutées depuis ce dossier, compilent le programme, vérifient la référence puis lancent quinze minutes de recherche dans la tranche attribuée.

```sh
c++ -O3 -std=c++17 circuits/matrix3-search.cpp -o /tmp/pequalnp-matrix3
/tmp/pequalnp-matrix3 --verify-baseline
/tmp/pequalnp-matrix3 900 > /tmp/pequalnp-matrix3-candidate.json
```

Une fin de délai sans témoin est enregistrée comme une recherche partielle. Le programme annonce explicitement ce statut dans son journal. Un candidat validé sur toutes les entrées passe ensuite par une preuve Lean de l’énoncé attribué et le vérificateur du projet.
