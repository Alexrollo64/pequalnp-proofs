# Recherche pequalnp du 26 novembre 2026

Ce dossier rassemble le travail de recherche effectué pour Alexrollo64 sur les unités du projet pequalnp. Les sources sont publiées sous la licence Apache 2.0 du dépôt. Le dossier contient des programmes, des constructions de référence et des résultats intermédiaires reproductibles.

| Suivi | État à la publication |
| --- | --- |
| Preuves complètes d’unités soumises au projet pendant ces sessions | 0 |
| Preuves acceptées par le vérificateur du projet pendant ces sessions | 0 |
| Fichiers de résultats Lean vérifiés localement | 5 |
| Formules SAT restreintes exclues avec un contrôle DRAT indépendant | 21 |
| Circuits de référence 4 × 5 vérifiés sur leurs vingt entrées | 14 |
| Recherche sur L-meta-21111 | Réservation rendue après essais sans témoin |
| Dernière recherche de graphe 4 × 6 | L-meta-23736, rendue sans témoin |

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

Les fichiers Lean ont été vérifiés avec Lean 4.36.0 et les dépendances du dépôt au commit `1b129350cb6ba392b73f11af10e914e9ef7c77fd`. Depuis le répertoire `lean` du dépôt, les commandes suivantes reconstruisent les définitions puis vérifient les fichiers.

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

La recherche sur L-meta-18919 porte sur le produit de deux matrices booléennes 3 × 3. Le bureau a attribué L-meta-18919, tranche 6 sur 16. Cette tranche impose un circuit d’au plus 44 portes, exactement une porte NON et de 23 à 33 portes ET. Les neuf sorties sont celles du produit booléen. Le programme cherche sur 512 entrées d’essai et contrôle tout candidat qui passe ces essais sur les 262 144 entrées possibles. La référence connue à 45 portes a passé ce contrôle complet. La réservation a été rendue après ces essais avec le motif out_of_time. [Données de l’attribution](circuits/active-search.json) · [Programme de recherche](circuits/matrix3-search.cpp)

Les commandes suivantes, exécutées depuis ce dossier, compilent le programme, vérifient la référence puis lancent quinze minutes de recherche dans la tranche attribuée.

```sh
c++ -O3 -std=c++17 circuits/matrix3-search.cpp -o /tmp/pequalnp-matrix3
/tmp/pequalnp-matrix3 --verify-baseline
/tmp/pequalnp-matrix3 900 > /tmp/pequalnp-matrix3-candidate.json
```

Une fin de délai sans témoin est enregistrée comme une recherche partielle. Le programme annonce explicitement ce statut dans son journal. Un candidat validé sur toutes les entrées passe ensuite par une preuve Lean de l’énoncé attribué et le vérificateur du projet.

## Vérification indépendante du produit matriciel

La référence à 45 portes dispose maintenant d’une preuve Lean locale utilisant le module ReplayColExpr fourni par le projet et autorisé pour cette unité. Ce contrôle sert à préparer la production d’une preuve pour un éventuel circuit à 44 portes. Le générateur utilise l’énoncé et les imports de l’attribution du bureau. Son contrôle de format a passé le validateur du client sur un fichier de test. [Référence Lean à 45 portes](L_meta_18919_schoolbook_replay.lean) · [Générateur de preuve](circuits/make-matrix3-proof.py)

Un second programme, écrit en Python, évalue les neuf sorties sur les 262 144 entrées au moyen de colonnes de vérité représentées par des entiers. Il confirme les 2 359 296 valeurs de sortie de la référence. Il donne également les erreurs de chaque sortie des candidats intermédiaires. [Vérificateur indépendant](circuits/verify-matrix3.py) · [Contrôle de la référence](circuits/experiments/matrix3-reference-45-verification.json)

Un candidat intermédiaire de la recherche structurée est conservé avec son contrôle complet. Il respecte la taille et les nombres de portes de la tranche. Le contrôle constate encore des valeurs de sortie incorrectes. Le fichier porte le statut de candidat rejeté. [Candidat intermédiaire](circuits/experiments/matrix3-rejected-candidate-v3.json) · [Résultats du contrôle complet](circuits/experiments/matrix3-rejected-candidate-v3-verification.json)

La variante structurée donne la priorité au partage d’intermédiaires entre les sorties et à l’utilisation de la porte NON. Ces critères guident la recherche. Les exemples ci-dessous lancent cette variante avec un checkpoint du meilleur candidat rencontré puis vérifient ce fichier.

```sh
/tmp/pequalnp-matrix3 660 20261128 /tmp/pequalnp-matrix3-best.json structured
python3 circuits/verify-matrix3.py /tmp/pequalnp-matrix3-best.json
```

Le statut de participation conserve zéro preuve complète soumise ou acceptée pendant ces sessions. Les données d’attribution et les résultats de vérification sont publiés au fur et à mesure du travail.


## Certificat SAT et recherche sur tables complètes

L’unité L-meta-22882 demandait cinq portes pour une fonction sur les entrées ayant une ou deux positions actives. La synthèse SAT sur les 21 entrées distinctes a conclu UNSAT. Le certificat DRAT a passé un contrôle indépendant avec drat-trim. La CNF et son certificat compressés sont conservés avec leurs empreintes. La correspondance entre ce modèle SAT et tous les circuits permis par l’énoncé reste à formaliser dans Lean ; aucune réfutation de cette unité n’a été soumise. Une construction de référence à six portes a été vérifiée dans Lean. [Résultat et portée](circuits/experiments/L-meta-22882-result.json) · [Référence Lean](L_meta_22882_reference.lean) · [Certificats](circuits/certificates)

```sh
gzip -dc circuits/certificates/L-meta-22882-full.cnf.gz > /tmp/pequalnp-22882.cnf
gzip -dc circuits/certificates/L-meta-22882-full.drat.gz > /tmp/pequalnp-22882.drat
/chemin/vers/drat-trim /tmp/pequalnp-22882.cnf /tmp/pequalnp-22882.drat
```

Pour le produit matriciel, une autre recherche conserve six sorties de référence et tente de calculer les trois autres en quatorze portes. Ses tables couvrent toutes les 4 096 affectations des douze variables concernées. Ce périmètre constitue une restriction de la tranche attribuée. Les recherches Python et C++ ont atteint leurs limites de temps sans témoin ; la tranche complète n’est pas épuisée. Les journaux conservent les améliorations et le statut final.

```sh
python3 circuits/matrix3-window.py --full-table
c++ -O3 -std=c++17 circuits/evolve-exact-window.cpp -o /tmp/pequalnp-window
/tmp/pequalnp-window 300 20261201 /tmp/pequalnp-window-best.json \
  < window-results/L-meta-18919-full-window.txt > /tmp/pequalnp-window-candidate.json
```

Le générateur de table et l’optimiseur C++ n’ont besoin ni de PySAT ni d’un accès réseau. Tout éventuel témoin doit encore être assemblé et contrôlé sur les 262 144 entrées de la matrice entière, puis passer la preuve Lean et les contrôles du projet.


## Unité L-meta-23736 : graphe 4 × 6

L’énoncé attribué demande dix portes AND/OR. Une construction de référence à onze portes a été reconstruite, vérifiée sur les 24 entrées permises puis vérifiée dans Lean 4.36.0. La synthèse directe par choix de porte retrouve ce contrôle positif lorsqu’on lui impose les choix du témoin connu. La recherche à dix portes continue sans témoin vérifié à ce checkpoint. [Énoncé et statut](circuits/current-unit.json) · [Référence Lean à onze portes](L_meta_23736_reference.lean) · [Synthèse directe](circuits/pair-synth.py)

```sh
/tmp/pequalnp-research-env/bin/python circuits/pair-synth.py \
  circuits/L-meta-23736-table.json /tmp/pequalnp-23736-candidate.txt
```

Cette recherche sélectionne deux fils antérieurs distincts et une opération AND/OR pour chaque porte. Elle écarte les portes sur entrées primaires qui sont constantes ou recopient un de leurs parents, et exige que chaque porte intermédiaire soit lue. Les options de tri et de lecture de toutes les entrées ajoutent d’autres restrictions lorsqu’elles figurent dans le fichier de paramètres. Un témoin reste contrôlé sur toutes les entrées puis dans Lean ; une absence de témoin ou un verdict UNSAT de ce modèle n’est pas une réfutation formelle de l’énoncé.


## Bilan des petites synthèses sur six entrées

Quatre unités attribuées ont été étudiées sur les 21 configurations distinctes à une ou deux entrées actives. Les CNF de recherche ont donné UNSAT aux tailles demandées. Pour L-meta-22882, L-meta-24212 et L-meta-22764, un certificat DRAT a également passé le contrôle indépendant. L-meta-24403 conserve uniquement le verdict du solveur de cette exécution. Les paramètres, énoncés attribués, empreintes des programmes et certificats, et limites de portée sont publiés dans le relevé. Aucune de ces observations n’est une réfutation Lean soumise au projet. [Relevé des quatre unités](circuits/experiments/two-lit-sat-results.json)

Les tables publiques permettent de régénérer les CNF et les certificats avec le solveur fourni. Le préfixe de sortie est dans /tmp. Par exemple :

```sh
/tmp/pequalnp-research-env/bin/python circuits/synth-circuit.py \
  circuits/L-meta-22764-table.json /tmp/pequalnp-22764-candidate.txt
/chemin/vers/drat-trim /tmp/pequalnp-L-meta-22764.cnf /tmp/pequalnp-L-meta-22764.drat
```

Sur L-meta-23736, la synthèse directe par choix de porte a aussi atteint sa limite de 150 secondes sans verdict. La recherche avec multiplexeurs a été interrompue sans verdict. La réservation a été rendue avec le motif out_of_time. La référence Lean à onze portes reste un contrôle positif ; l’objectif à dix portes demeure non démontré. Le bilan des preuves complètes soumises et acceptées reste zéro.

## Sorties des circuits à six entrées

Le 26 novembre, Lean 4.36.0 a vérifié la correspondance entre les 36 paires ordonnées et les 21 configurations du modèle SAT. Sur ces configurations, les tables des unités L-meta-22882, L-meta-24212, L-meta-24403 et L-meta-22764 exigent respectivement 4, 5, 6 et 5 coordonnées. Pour chacune, la sortie de tout circuit correct doit désigner une porte existante. Le théorème `output_is_gate` exclut à la fois les six fils d’entrée et les indices au-delà du dernier fil. Son énoncé permet une porte intermédiaire. Il reste à relier un circuit admissible au codage SAT complet en préservant le budget de portes. [Preuve auxiliaire vérifiée](TwoLitTables.lean)

Le théorème `last_gate_solution` justifie ensuite le choix de la dernière porte comme sortie pour ces quatre cibles. Il conserve le préfixe des portes du circuit jusqu’à la sortie, préserve toute condition individuelle sur les portes, et donne les mêmes valeurs sur les 64 entrées de longueur six. Le nombre de portes peut diminuer. Le passage à un budget exact et les autres contraintes du générateur SAT restent à établir.

### Budget exact

Lean 4.36.0 a vérifié `exact_budget_solution`. Pour les quatre tables, tout circuit correct de taille au plus B donne un circuit de taille exactement B avec sortie sur la dernière porte et mêmes valeurs sur toutes les entrées de longueur six. Chaque porte ajoutée calcule `AND(s,s)` où `s` est la sortie précédente. Toute condition individuelle sur les portes autorisant ces copies est préservée. Les fichiers de paramètres des quatre expériences autorisent deux parents égaux et laissent désactivée la contrainte optionnelle de minimalité. Le théorème ne traite pas encore les lectures de fils inexistants, les constantes, ni la traduction intégrale en clauses CNF. [Fichier Lean](TwoLitTables.lean)

La preuve `Normalization.exact_budget_legal` intègre ensuite la normalisation de L-meta-10422 (source amont créditée dans le fichier). Dans le circuit de taille exacte, toute porte lit exclusivement des fils déjà disponibles et une porte NON a au plus un parent. Les portes sans parent peuvent encore représenter des constantes. La prochaine étape est de propager ces constantes et les alias sans dépasser le budget, avant la traduction complète en clauses SAT. Ce résultat auxiliaire a passé Lean 4.36.0 le 26 novembre à 22 h 38 (Paris).

### Propagation des constantes et des copies

Lean 4.36.0 a vérifié `eliminate_constants` et `translate_fits`. Pour toute longueur d’entrée fixée et tout circuit ET/OU/NON non constant dont chaque porte lit au plus deux fils, la traduction préserve la sortie sur toutes les entrées de cette longueur et utilise au plus autant de portes. Elle propage les constantes et les références directes, traite les lectures hors limites selon la sémantique officielle, et émet seulement des ET/OU binaires à parents triés ou des NON unaires sur des fils déjà disponibles. La preuve se fait par induction sur la liste des portes. La prochaine étape consiste à composer cette traduction avec le choix de la sortie et le budget exact, puis à construire une affectation satisfaisant toutes les clauses, y compris les variables auxiliaires des contraintes de cardinalité. [Preuve vérifiée](ConstantPropagation.lean)

### Forme complète du circuit et vérification LRAT du 27 novembre

`structural_iff` démontre dans les deux sens, pour les quatre tables et tout budget, l'équivalence entre l'énoncé utilisant le prédicat officiel `FanInTwo` et un circuit de taille exacte, à sortie finale, à parents antérieurs triés pour ET/OU et à parent unique pour NON. La preuve conserve la même forme de circuit au cours de la suppression des constantes, de la troncature et du remplissage. [Preuve](SynthesisNormalForm.lean)

Pour L-meta-22882, le DIMACS publié contient 616 variables et 4 732 clauses (SHA-256 `d7f6f9963d64f36452eed5d8fdcdc706482a994e2cf19e2a3c3daf7dbb10d072`). CaDiCaL 2.1.2 a régénéré un certificat LRAT texte de 16 509 actions (SHA-256 `2e6aa4dc01c383c15fc35baa25645f46180246cb6740a22d9bddb98278a862e5`). Le vérificateur LRAT de la bibliothèque standard Lean 4.36.0 l'a accepté après une conversion aller-retour identique octet par octet du DIMACS. Un nombre de clauses erroné et un certificat tronqué ont été rejetés. Il s'agit d'une exécution du vérificateur sur cette formule. Il reste à construire l'affectation des clauses du DIMACS à partir d'un circuit en forme normale pour en déduire la réfutation du lemme. [Vérificateur](ReplayDimacs.lean)

Depuis ce dossier avec la version du projet de Lean et le CaDiCaL indiqué, la vérification du certificat se reproduit ainsi :

```sh
gzip -dc circuits/certificates/L-meta-22882-full.cnf.gz > /tmp/L22882.cnf
cadical --lrat --no-binary /tmp/L22882.cnf /tmp/L22882.lrat
# CaDiCaL retourne 20 pour UNSAT.
lean --run ReplayDimacs.lean /tmp/L22882.cnf /tmp/L22882.lrat
```

Pour compiler `SynthesisNormalForm.lean`, compiler d'abord les modules voisins `ConstantPropagation.lean` et `TwoLitTables.lean` en .olean et ajouter leur dossier à LEAN_PATH dans l'environnement Lake du projet.

### Numérotation et clauses de sélection pour L-meta-22882

Le générateur Lean [FiveGateCNF.lean](FiveGateCNF.lean) reconstruit les 4 732 clauses du fichier certifié à partir des six colonnes, des cinq portes et de la table de sortie. Le 27 novembre, [CheckFiveGateCNF.lean](CheckFiveGateCNF.lean) a comparé l'écriture DIMACS de cette formule au fichier publié, identique octet par octet. Un en-tête modifié a été rejeté.

Lean a vérifié `allocated` (la numérotation de toutes les variables de 1 à 616), `one_complete` (les bits auxiliaires du compteur décrivent si le choix a déjà été rencontré) et `selector_blocks`. Pour chaque trace de calcul satisfaisant les hypothèses et chacune des cinq portes, la même affectation satisfait les trois blocs qui imposent un choix unique du fil gauche, du fil droit et de l’opération. La génération et la comparaison couvrent aussi les autres clauses. Pour la preuve d’impossibilité, il reste à démontrer leur satisfaction par cette affectation, à extraire la trace depuis le circuit normalisé et à assembler le certificat dans une preuve de l’énoncé exact.

Pour reproduire la comparaison dans l’environnement Lake du projet, placer `TwoLitTables.olean` et `FiveGateCNF.olean` dans le chemin de modules, puis lancer `lean --run CheckFiveGateCNF.lean /tmp/L22882.cnf` sur le DIMACS décompressé.

### 27 novembre 2026, session de 02 h 35 (Paris)

Pour L-meta-22882, `TraceClauses.lean` démontre dans Lean 4.36.0 que toute trace du modèle normalisé à cinq portes satisfait les 4 732 clauses de la formule exacte. Le théorème `no_trace_of_unsat` prend l’insatisfiabilité comme hypothèse. La conversion d’un circuit arbitraire admissible en trace et l’intégration du certificat comme théorème fermé restent à établir. Le bureau indique `not_open` pour cette unité.

`EmitTwoLitCNF.lean` généralise l’export aux autres budgets et cibles. Avec les dépendances du journal sur LEAN_PATH, la commande `lean --run EmitTwoLitCNF.lean BUDGET CIBLE instance.cnf` produit le DIMACS. CaDiCaL 2.1.2 (`cadical --lrat --no-binary instance.cnf cert.lrat`) puis ReplayDimacs.lean ont donné les contrôles suivants à 02 h 39 Paris.

| Unité | Budget | Cible | Variables / clauses | Actions LRAT acceptées | SHA-256 du DIMACS | SHA-256 du LRAT |
|---|---:|---:|---|---:|---|---|
| L-meta-24212 | 6 | 310267 | 726 / 5945 | 44412 | 184502d3d73526139045c16e4e68ae539be44cf192b1d8d39c928d491f3b82b9 | 2b2111367f15673d940d96c66de1a889344bb6c4e24e8fa28f31acc0cd79ebed |
| L-meta-22764 | 5 | 413 | 616 / 4732 | 7229 | 14ab4000b3d5711a6beab952707dfcec5867f161ad276f28dc2e1acf29efe3d8 | a86895af29866ed95d2cff47b9877c58b5016eb34364b0a6281ecd63a39f7ac9 |

Pour L-meta-24403 (budget 8, cible 6077), le nouvel essai limité à 60 secondes s’est terminé sans verdict, code de sortie 0. Aucun certificat complet issu de cet essai. Ces contrôles portent sur les formules finies. Aucune preuve d’unité soumise dans cette session.

### L-meta-20782 — minimum exact de huit portes (27 novembre 2026)

Le noyau de Lean 4.36.0 vérifie dans [Mask31917056Lower.lean](Mask31917056Lower.lean) la négation exacte de la borne de sept portes pour le masque 31917056 sur 5 × 5. Les huit fils d’entrée indispensables obligent chacune de sept portes éventuelles à augmenter d’une unité le nombre de fils demandés en remontant depuis la sortie. Chaque porte doit donc remplacer un fil par deux fils distincts disponibles sans partage à cette étape. Sur sept couples d’essai, le poids de la sortie vaut sept et la somme des poids aux entrées indispensables vaut six. Les inégalités pour ET et OU sont toutes contrôlées par le noyau. [seven-test-weights.py](seven-test-weights.py) reproduit la table de poids. La construction à huit portes dans le théorème amont `PEqualNP.Outside.L_meta_20709` a aussi été recompilée. Ces deux bornes donnent le minimum exact pour cette table.

Unité attribuée à 02 h 42 (Paris), renouvelée deux fois et rendue à 02 h 53 avec le motif confirmé `statement_seems_false`. Le bureau avait attribué le sens positif. Cette publication documente la réfutation locale. Le score et le verdict du projet dépendent de sa procédure de soumission.

### 27 novembre, 03 h 39 à Paris — restriction à une sous-matrice

[PaddedRows.lean](PaddedRows.lean) vérifie trois résultats dans Lean 4.36.0. Toute représentation monotone ET/OU d’un graphe biparti se restreint, au même budget, à une sélection quelconque de lignes et de colonnes. Un graphe contenant le masque 31917056 en sous-matrice induite exige donc au moins huit portes. Enfin, ajouter un nombre arbitraire de lignes vides au graphe initial laisse son minimum exactement à huit. La construction réutilise le témoin à huit portes de L-meta-20709. La borne inférieure est constante. Les trois théorèmes dépendent seulement de propext, Classical.choice et Quot.sound.

Pour reproduire le contrôle, construire le module amont PEqualNP.Outside.L_meta_20709, compiler Mask31917056Lower.lean en .olean, puis compiler PaddedRows.lean avec ce répertoire sur LEAN_PATH. Travail de recherche indépendant pendant le délai du bureau.

### 27 novembre, 04 h 40 à Paris — copies disjointes du masque 31917056

[DisjointCopies.lean](DisjointCopies.lean) démontre que représenter k copies disjointes du graphe de L-meta-20782 exige au moins 8k portes ET/OU à deux entrées, même si des portes communiquent entre blocs. Chacune des k copies a huit fils indispensables. Cela donne d’abord 8k − 1. À égalité, toutes les expansions en remontant depuis la sortie sont saturées. Le certificat à sept configurations de la première copie donne alors un poids de sortie de sept pour un poids total d’entrée de six, les fils des autres blocs ayant un poids nul. Cela exclut l’égalité pour k positif. La borne est vérifiée par le noyau Lean 4.36.0 pour tout k. Le minimum exact pour k supérieur à un reste à établir. Pour reproduire, compiler PaddedRows.lean et sa dépendance locale en .olean avant de vérifier DisjointCopies.lean dans le même environnement.

Pour deux copies, le théorème upper_two construit explicitement 17 portes et en vérifie les 100 entrées promises dans Lean. Avec la borne de 16 portes donnée par lower, il reste exactement deux valeurs possibles, 16 et 17.

### 27 novembre, 05 h 39 à Paris — coût exact des formules sans partage

Pour k ≥ 1 copies disjointes du masque 31917056, une formule binaire ET/OU correcte sur les entrées promises a besoin d’exactement 9k − 1 portes au minimum. [TreeCopies.lean](TreeCopies.lean) démontre la borne inférieure dans `formula_lower` et construit un témoin dans `optimum_tree`. Fixer à faux toutes les entrées extérieures à une copie permet de supprimer des branches de la formule. La borne de huit portes sur une copie impose au moins neuf occurrences de feuilles pour chaque copie. Les ensembles de feuilles ainsi comptés sont disjoints. Réciproquement, relier k formules à huit portes par k − 1 portes OU atteint cette borne.

Pour deux copies, cela donne 17 portes sans partage. Un circuit à 16 portes devrait donc réutiliser un résultat intermédiaire. Son existence reste à trancher. Pour reproduire, compiler DisjointCopies.lean en .olean avec les dépendances indiquées ci-dessus, puis compiler TreeCopies.lean avec le même LEAN_PATH. Lean 4.36.0 a contrôlé les deux théorèmes, dont les seuls axiomes signalés sont propext, Classical.choice et Quot.sound. Résultat auxiliaire du journal, sans attribution d’unité.

### 27 novembre, 06 h 38 à Paris — contraintes sur les circuits à 16 portes

[OneDefect.lean](OneDefect.lean) considère deux copies disjointes du masque 31917056 avec partage autorisé. En remontant depuis la sortie, on remplace chaque sortie demandée par ses entrées. Le nombre de fils distincts demandés croît d’au plus un par porte. Le théorème `candidate` démontre que, pour tout circuit correct de taille au plus 16, on aboutit exactement aux 16 fils indispensables, et que le déficit total par rapport à une croissance de un à chaque étape vaut un. Il y aurait donc quinze augmentations de un et une étape à effectif constant.

Le théorème `both_blocks` montre que cette unique étape doit augmenter le poids du certificat sur chacune des deux suites de sept tests. La sortie de sa porte doit notamment être vraie sur au moins un test de chaque copie. Le minimum général pour ces deux copies reste compris entre 16 et 17. Pour reproduire, compiler ce fichier sous Lean 4.36.0 avec DisjointCopies.olean et ses dépendances sur LEAN_PATH. Les deux théorèmes ont été vérifiés avec propext, Classical.choice et Quot.sound.

### 27 novembre, 07 h 38 à Paris — le fil partagé doit être actif sur les deux copies

[SharedOperand.lean](SharedOperand.lean) précise la contrainte sur un éventuel circuit à 16 portes pour deux copies du masque 31917056. En remontant à la porte exceptionnelle, au plus un de ses opérandes figure déjà parmi les autres fils demandés. Sur chacune des deux suites de sept tests, la sous-additivité du poids des opérandes oblige ce chevauchement à contenir un fil de poids strictement positif. Il s’agit donc du même fil sur les deux suites. Le théorème `candidate_shared` situe ce fil parmi les sorties de portes antérieures et exclut toutes les entrées primaires.

Si ce fil est lui-même produit par une porte binaire directement reliée à deux entrées primaires, `raw_pair` impose un OU entre une entrée de chaque copie. Sur ces suites, six entrées par copie peuvent convenir, soit 36 paires possibles à ce stade. L’existence d’un circuit utilisant l’une de ces paires reste ouverte, tout comme le cas d’un sous-circuit partagé plus profond. Pour reproduire, compiler OneDefect.lean et ses dépendances en .olean, puis vérifier SharedOperand.lean avec le même LEAN_PATH sous Lean 4.36.0.

### 27 novembre — fusion exclusive des 36 paires d’entrées primaires

[FusionCriterion.lean](FusionCriterion.lean) classe les paires retenues dans SharedOperand.lean lorsque le reste du circuit reçoit leur OU et perd l’accès individuel aux deux signaux. Parmi les 36 paires, les 9 paires de lignes et les 9 paires de colonnes confondent des configurations exigeant des réponses différentes. Les 18 paires ligne-colonne entre copies préservent suffisamment d’information. Le théorème général `mixed_iff` caractérise une telle fusion pour toute relation bipartie sur des entrées où exactement une ligne et une colonne sont actives. Si la case au croisement des deux signaux vaut zéro, la fusion permet un décodage monotone. Si elle vaut un, il faut et il suffit que toute sa ligne et toute sa colonne valent un.

Pour chacune des 18 paires restantes, `mergedCircuit` place le OU en première porte et redirige les lectures des deux entrées vers sa sortie. Les théorèmes `exclusive`, `merged_size`, `merged_legal` et `merged_correct` vérifient cette redirection, la taille de 18 portes, les opérations autorisées et les 100 sorties promises par paire. Le témoin général antérieur reste meilleur avec 17 portes. Le budget de 16 portes et les fils partagés construits par plusieurs portes restent ouverts. Pour reproduire, compiler les dépendances jusqu’à SharedOperand.olean, puis vérifier FusionCriterion.lean sous Lean 4.36.0 avec le même LEAN_PATH.

### 27 novembre, 09 h 44 à Paris — L-meta-20782 et le partage d’une porte OU

Pour les deux copies disjointes du masque 31917056, `RepeatedInput.lean` démontre une borne inférieure de 17 portes si la seule porte dont le résultat peut être partagé est un OU entre une entrée de ligne d’une copie et une entrée de colonne de l’autre. Cette porte compte dans le total. La formule ET/OU qui suit peut utiliser son résultat et les entrées brutes autant de fois que nécessaire. La borne couvre les deux orientations et tous les choix de ligne et de colonne.

Sur une seule copie, si une formule correcte répète une seule entrée distincte, celle-ci doit être la cinquième ligne (indice 4). Le script `check-repeat-weights.py` reproduit indépendamment les cinq tables utilisées dans la preuve et contrôle les deux inégalités de sous-additivité sur 81 920 paires. Lean 4.36.0 a compilé `classification` et `mixed_lower` avec `TreeCopies` et ses dépendances sur le chemin des imports. Les deux théorèmes dépendent de `propext`, `Classical.choice` et `Quot.sound`. La question des 16 portes avec partage d’autres résultats intermédiaires reste ouverte dans ce travail. Il s’agit d’une preuve auxiliaire du journal de recherche.

### 27 novembre, 10 h 45 à Paris — nécessité de chaque porte au budget de 16

[PruneGate.lean](PruneGate.lean) établit `essential_gate` pour k copies du masque 31917056, au budget de 8k portes ET/OU. Chaque porte doit avoir une entrée positive témoin sur laquelle forcer sa sortie à zéro rend la sortie finale fausse. La preuve supprime physiquement la porte et renumérote les fils qui suivent. Sans témoin, la monotonie préserve les sorties négatives et la suppression contredirait la borne de 8k portes. Le circuit peut partager arbitrairement ses fils.

Pour deux copies, `and_pair` et `one_read` imposent que les deux entrées brutes d’une porte ET soient simultanément actives sur une arête. `count_pairs` compte 16 paires admissibles sur 190 paires distinctes non ordonnées. Une énumération Python indépendante a également donné 16 paires admises et 174 exclues. La condition s’applique à toute position de la porte. La prochaine recherche peut imposer un témoin positif par porte et ces exclusions dans l’encodage à 16 portes. Le budget reste ouvert.

[FalseSupport.lean](FalseSupport.lean) traite en plus une formule alimentée par plusieurs signaux auxiliaires qui ne s’allument que sur des entrées négatives. Sa partie formule exige à elle seule au moins 17 portes pour deux copies. Les deux fichiers auxiliaires ont compilé avec Lean 4.36.0. Pour reproduire, compiler `TreeCopies` et ses imports du journal et le module amont `PEqualNP.Outside.L_meta_2606`, puis vérifier les deux fichiers dans le même environnement Lean.

### 27 novembre — Six entrées indispensables pour la recherche à 16 portes

Pour les deux copies du masque 31917056, [EdgeEdits.lean](EdgeEdits.lean) construit six circuits ET/OU. Chacun donne la bonne réponse sur 99 des 100 entrées et se trompe sur une entrée différente. Les quatre faux négatifs isolés sont (2,0), (4,4), (7,5) et (9,9), avec 15 portes. Les deux faux positifs sont (3,4) et (8,9), avec 16 portes. Les coordonnées commencent à zéro. Lean vérifie les témoins sur le type Circuit du projet. Si un jeu de tests omet une de ces six entrées, un circuit de 16 portes au plus passe tous ses tests tout en donnant une réponse fausse sur l’entrée omise. Le caractère suffisant des six tests reste ouvert.

Pour les formules binaires monotones en arbre, le théorème `optimum` donne aussi le minimum exact après suppression de n’importe quel sous-ensemble de ces quatre arêtes. Pour d arêtes supprimées, le minimum est 17 − 2d. Le témoin enlève deux portes par arête. Dans l’autre sens, une porte ET et une porte OU par arête suffisent à restaurer la formule originale, dont le minimum est 17. Cette conclusion sur le nombre minimal de portes concerne les formules sans partage intermédiaire. L’existence d’un circuit exact à 16 portes avec partage reste ouverte.

Reproduction des recherches depuis ce dossier avec Python 3 et un compilateur C++17 :

- `python reference-repair.py` teste 6 130 880 descriptions de modifications de la référence à 17 portes (une suppression avec redirection globale et une réécriture binaire). Plusieurs descriptions peuvent produire le même circuit. Le minimum observé dans ce voisinage est une erreur.
- `python rectangle-witnesses.py` cherche des couvertures de rectangles après inversion de chacune des 100 cases.
- `g++ -O3 -std=c++17 block-formulas.cpp -o block-formulas && ./block-formulas` énumère les tables distinctes des formules de taille au plus sept sur une copie, y compris les dix configurations avec une seule entrée active. Ces scripts servent à trouver les témoins. Les résultats formels se reproduisent en compilant EdgeEdits.lean avec TreeCopies et ses dépendances dans le chemin des imports.

### 27 novembre — Au moins 18 tests pour le budget de 16 portes

[EighteenTests.lean](EighteenTests.lean) prouve que tout jeu de tests qui détecte chaque circuit ET/OU incorrect d’au plus 16 portes pour les deux copies doit contenir au moins 18 cases. [TestPacking.lean](TestPacking.lean) fournit 16 circuits dont les ensembles d’erreurs sont non vides et deux à deux disjoints. Dans chacun des deux blocs, trois paires d’erreurs imposent déjà trois choix de tests. Parmi huit autres circuits, il en reste toujours un dont les erreurs évitent ces trois choix. Il faut donc deux tests supplémentaires. Les témoins utilisent le type Circuit du projet. Compiler les fichiers dans l’ordre TreeCopies, EdgeEdits, TestPacking, EighteenTests, avec les imports du journal. Les contrôles d’axiomes de ces deux nouveaux théorèmes donnent propext, Classical.choice et Quot.sound.

La définition `suite` fixe 18 cases. Lean vérifie que cette suite rencontre toutes les familles d’erreurs utilisées dans cette preuve. Pour les formules binaires sans partage, les programmes C++ calculent les coûts minimaux des 262 144 réponses possibles sur ces cases. La réponse du graphe est la seule ayant un coût de 17 portes. Toutes les autres sont réalisables avec 16 portes ou moins. Ce décompte exhaustif est vérifié par deux algorithmes indépendants. La certification Lean porte sur la borne de 18 tests et ses témoins. Pour reproduire le calcul des coûts :

```bash
g++ -std=c++17 -O3 suite-formula.cpp -o suite-formula
g++ -std=c++17 -O3 verify-suite-costs.cpp -o verify-suite-costs
./suite-formula costs.bin
./verify-suite-costs costs.bin
```

Le premier programme compte les combinaisons à chaque coût par transformation zêta et inversion de Möbius. Le second vérifie pour chaque table le minimum sur toutes les décompositions possibles de la porte de sortie. Empreinte SHA-256 des 262 144 octets de coûts : `fc2975a6904b40fa7f344090be6bb8ddaee0a1c0440d419119a25f3c8d6c4d2c`.

[refine-tests.py](refine-tests.py) cherche séparément des circuits avec partage. Il essaie des circuits binaires à opérandes distincts utilisant les 16 entrées brutes requises et toutes les portes intermédiaires. Chaque candidat SAT est rejoué sur les 100 cases avant d’ajouter sa première erreur à la suite. [refinement.jsonl](refinement.jsonl) part des six cases précédentes, trouve et élimine 20 candidats, puis atteint sa limite de 15 secondes sur 26 cases. [packing-refinement.jsonl](packing-refinement.jsonl) en élimine sept depuis une autre suite initiale de 16 cases, puis atteint sa limite de 25 secondes sur 23 cases. Le lancement direct sur les 18 cases publiées a atteint sa limite de 12 secondes sans verdict. Le budget général de 16 portes reste ouvert. La prochaine piste est d’exploiter le fait qu’un candidat exact à ce budget doit partager au moins un résultat intermédiaire, même pour satisfaire ces seules 18 cases.

### 27 novembre — Au moins 20 tests pour les circuits de 16 portes

Sur les deux copies disjointes du graphe de L-meta-20782, toute suite de tests qui détecte chaque circuit ET/OU incorrect d’au plus 16 portes doit contenir au moins 20 cases. La borne précédente était de 18. [TwentyTests.lean](TwentyTests.lean) construit 36 circuits incorrects et répartit les 100 cases en six régions disjointes. Détecter les erreurs de ces circuits exige au minimum 6, 4, 4, 2, 2 et 2 cases dans les régions respectives. Le noyau Lean vérifie le comptage, les erreurs et les budgets. Une suite explicite de 20 cases détecte les 36 témoins. [TwentyCounterexample.lean](TwentyCounterexample.lean) vérifie un autre circuit de 16 portes qui passe ces 20 tests et se trompe sur 11 des 100 cases. La suffisance d’une autre suite de 20 cases reste ouverte.

[SharedSuite.lean](SharedSuite.lean) donne une borne plus forte pour la suite précise de 18 cases publiée précédemment. Quatre circuits de 16 portes la passent, chacun en lisant deux fois la sortie de sa première porte OU. Leurs nombres d’erreurs respectifs sont 2, 2, 16 et 16. Leurs ensembles d’erreurs sont deux à deux disjoints. Toute suite complète conservant ces 18 cases doit donc en compter au moins 22. Pour reproduire les preuves, compiler les fichiers du journal jusqu’à EighteenTests, puis SharedSuite, TwentyTests et TwentyCounterexample, dans cet ordre, avec Lean 4.36.0.

Le calcul exhaustif [shared-suite.cpp](shared-suite.cpp) donne une porte OU précalculée à une formule ET/OU de 15 portes au plus et laisse aussi toutes les entrées brutes disponibles. Parmi les 36 paires du lemme antérieur `raw_pair`, seules (4,16) et (11,9) permettent de passer les 18 tests. Toutes les formules qui y parviennent coûtent 15 portes en plus du OU. Le programme relève leurs tables sur 100 cases en combinant toutes les décompositions de coût minimal. Il obtient 144 et 224 tables, dont une commune. Quatre cases supplémentaires suffisent à éliminer les 367 tables de cette famille. Les résultats du programme et les quatre témoins contrôlés par Lean ont des portées distinctes. Les circuits dont la porte partagée dépend de plusieurs étages restent à étudier.

```bash
g++ -O3 -std=c++17 shared-suite.cpp -o shared-suite
python shared-suite-counts.py
```

[Résultats de l’énumération](shared-suite-counts.json) · [Recherche SAT sur la nouvelle suite](twenty-refinement.jsonl). Après ajout de la case (2,6), la recherche à 21 cases a atteint sa limite de 45 secondes avec le statut UNKNOWN. La valeur 20 concerne la taille des tests. Le coût optimal du circuit sur les deux copies reste compris entre 16 et 17 portes.

### 27 novembre — Minimum exact de 16 portes pour deux copies

[ExactTwoCopies.lean](ExactTwoCopies.lean) établit que deux copies disjointes du graphe de masque 31917056 admettent un circuit ET/OU de budget `n` si et seulement si `16 ≤ n`. La construction précédente coûtait 17 portes. Le nouveau circuit réalise le graphe sur les 100 entrées promises, y compris les cases entre les blocs. Le noyau Lean vérifie la construction et sa taille. La borne inférieure utilise le théorème `DisjointCopies.lower` du journal. Le même fichier vérifie un circuit de 25 portes pour trois copies sur les 225 entrées et exclut tout budget inférieur à 24. Il reste à déterminer si 24 portes suffisent pour trois copies.

Le circuit calcule d’abord le OU des colonnes 1, 2 et 3 du premier bloc avec la ligne 9 du second bloc (indices à partir de zéro). Deux portes en aval lisent ce même signal. Le partage économise une porte par rapport au meilleur arbre de calcul. [Expression du circuit](two-copy-expression.json) · [Vérification Python indépendante des 100 cases](check-witness.py).

Pour trouver ce signal, on a partitionné les 16 fils primaires indispensables. Une partie est lue exclusivement par un sous-circuit qui n’envoie qu’un bit au reste du circuit. [SingleBitFactor.lean](SingleBitFactor.lean) caractérise l’existence d’un tel codage et d’un décodeur monotone, indépendamment de leurs coûts. Si le décodeur ne peut distinguer une case positive d’une négative avec les seuls fils extérieurs, le bit partagé doit valoir respectivement un et zéro. Le critère vérifie si toutes ces obligations sont compatibles avec la monotonie et construit un code et un décodeur quand elles le sont.

Sur les 65 536 choix possibles, le [programme de dénombrement](single-bit-factors.cpp) en retient 116. Il en reste 45 en exigeant au moins deux fils et la possibilité d’activer le bit sur au moins un des sept tests de chacun des deux blocs. Ces nombres proviennent du calcul C++. Le [programme de synthèse](separator.py) prend ensuite le OU choisi comme entrée disponible deux fois. À chaque porte OU, il répartit les échantillons positifs entre les deux branches. À chaque porte ET, il répartit les négatifs. Les deux branches consomment des occurrences distinctes des fils disponibles. Le programme retrouve la formule publiée pour le support 928, dont les bits indexent la liste `WIRES` du programme.

```bash
g++ -O3 -std=c++17 single-bit-factors.cpp -o single-bit-factors
./single-bit-factors > single-bit-factors.csv
python separator.py 928
python check-witness.py
```

La vérification Lean utilise la version 4.36.0 du projet et le module DisjointCopies compilé. Le théorème porte sur le graphe à deux copies, étudié en complément de l’unité L-meta-20782 qui concerne une seule copie. Le résultat est publié dans le journal de recherche du fork.

### 27 novembre — Ce qu’impliquerait un circuit à 24 portes pour trois copies

Pour trois copies disjointes du graphe de masque 31917056, le minimum vérifié en Lean se situe entre 24 et 25 portes ET/OU, bornes incluses. Le résultat à deux copies reste exactement 16. Cette recherche prolonge le cas à une copie de L-meta-20782.

[CommonThree.lean](CommonThree.lean) donne une condition nécessaire sur les circuits du projet. Si 24 portes suffisent, la remontée depuis la sortie atteint exactement les 24 entrées indispensables. À une étape, une porte utilise un intermédiaire déjà présent parmi les fils nécessaires. Le même intermédiaire a un poids strictement positif dans chacun des trois jeux de sept tests. Le théorème `candidate_joint` et ses dépendances ont passé la vérification du noyau de Lean 4.36.0 avec les axiomes usuels.

On examine ensuite une forme de circuit plus précise. Un arbre ET/OU lit une fois ses entrées privées et produit un bit. Un second arbre lit chaque entrée extérieure au plus une fois et peut employer ce bit deux fois. Sur deux blocs à la fois, on retient les lignes 0, 2, 3, 4 et les colonnes 0, 1, 4, soit 48 cases. Les six coordonnées pertinentes de chaque bloc sont les lignes 2, 3, 4 et les colonnes 0, 1, 4. La ligne 0 est absente du support indispensable. Les colonnes 2 et 3 sont éteintes sur ces tests.

Si les entrées extérieures d’une case positive sont incluses dans celles d’une case négative, la monotonie impose que le bit partagé vaille respectivement un et zéro. Ses valeurs doivent aussi respecter la monotonie sur les entrées privées. Enfin, sur les sept tests du certificat de poids, si le bloc a k coordonnées privées, le poids w du bit satisfait w ≤ k et 7 ≤ 6 − k + 2w. La première inégalité compte chaque entrée de l’arbre privé une fois. La seconde compte le bit deux fois dans l’arbre extérieur.

Le [calcul Python](three-copy-partitions.py) énumère les 4 096 répartitions ordonnées sur une paire de blocs. Les 19 qui passent ce filtre sont les 18 paires formées d’une ligne seule et d’une colonne seule, dans les deux ordres, et la paire de masques (9, 9). Pour trois blocs, la seule répartition qui passe sur chaque paire est (9, 9, 9). Dans chaque bloc, la ligne 2 et la colonne 0 sont alors privées parmi les coordonnées testées. [PairFilter.lean](PairFilter.lean) contrôle l’implication sur les contraintes binaires explicites avec `bv_decide`. Son contrôle du certificat LRAT dépend de l’évaluation native de Lean. La déduction du triplet à partir de la liste des paires (`triangle`) utilise uniquement les axiomes usuels.

Pour le dernier triplet, on fixe le bit partagé à sa valeur sur l’entrée privée nulle. Dans un bloc, les cases (4,0), (0,1), (3,1), (4,1), (3,4), (4,4) ont pour sorties 0, 0, 1, 1, 0, 1. Sur les trois positives, les coordonnées privées sont déjà nulles. Sur les négatives, abaisser le bit préserve la sortie zéro. Les quatre fils restants ont un poids total de 4, et la cible pèse 5. Le noyau vérifie la sous-additivité du poids et l’obstruction après fixation du bit sous ses hypothèses explicites dans [FourWireCore.lean](FourWireCore.lean), théorème `clamped_obstruction`.

Pour reproduire le dénombrement, exécuter `python three-copy-partitions.py` dans ce répertoire. Le passage de la trace de partage de `candidate_joint` à la décomposition en deux arbres, puis aux hypothèses exactes des filtres et du dernier théorème, reste à formaliser. Cette étape manque pour conclure que 25 est optimal pour les circuits du projet.

### 27 novembre — Décomposition vérifiée de tout candidat à 24 portes

Pour trois copies du graphe de masque 31917056, [CutTrees.lean](CutTrees.lean) démontre le passage du circuit aux deux arbres ET/OU qui manquait à l’étape précédente. Le théorème `decompose` part d’un circuit du projet qui représente ce graphe en au plus 24 portes. Il construit deux formules. Ensemble, elles lisent chacune des 24 entrées indispensables exactement une fois. La seconde formule lit en plus deux occurrences du résultat de la première. Leur composition donne la valeur du circuit pour **toute liste de 30 booléens**, y compris en dehors de la promesse sur les entrées. La correction pour le graphe lui-même porte sur les entrées promises.

[WireUses.lean](WireUses.lean) établit que toutes les portes sont actives, lisent deux fils distincts et ne lisent que des fils déjà disponibles. Le comptage inclut les 48 lectures des portes et la lecture de la sortie. Il y a 48 fils indispensables ou produits, dont un seul est lu deux fois. La preuve coupe ce fil, additionne les occurrences de feuilles aux entrées et aux sorties de chaque porte, puis simplifie les termes intermédiaires. Le second fichier construit les arbres et vérifie par induction que brancher le premier sur le second reproduit l’évaluation du circuit.

Vérification locale sous Lean 4.36.0, dans l’ordre `WireUses` (importe `CommonThree`) puis `CutTrees` (importe aussi `TreeCopies`). Pour `decompose`, Lean indique uniquement les axiomes usuels `propext`, `Classical.choice` et `Quot.sound`. Ce résultat auxiliaire n’utilise pas le certificat natif du filtre fini de la session précédente.

La prochaine étape consiste à déduire des deux arbres les contraintes précises de monotonie et de coût de [PairFilter.lean](PairFilter.lean), puis à appliquer [FourWireCore.lean](FourWireCore.lean) au dernier masque. L’optimum formel est toujours compris entre 24 et 25 inclus. Aucun énoncé d’unité n’est soumis par cette mise à jour.

### 27 novembre — Trois copies exigent exactement 25 portes

[ExactThreeCopies.lean](ExactThreeCopies.lean) démontre `RepSizeAtMost (graph 3) n ↔ 25 ≤ n`. Le circuit de 25 portes figurait déjà dans [ExactTwoCopies.lean](ExactTwoCopies.lean). La nouvelle borne inférieure utilise la décomposition de [CutTrees.lean](CutTrees.lean). Elle exclut tous les circuits ET/OU à au plus deux entrées et de taille au plus 24 qui représentent les trois copies sur la promesse. La preuve se passe du filtre SAT et de toute évaluation native. Le noyau de Lean 4.36.0 rapporte uniquement `propext`, `Classical.choice` et `Quot.sound` pour le théorème final.

Dans chacun des trois blocs, on retient six cases sur lesquelles quatre fils ont un poids total de 4, alors que la sortie a un poids de 5. [PositiveCore.lean](PositiveCore.lean) en tire deux conséquences pour les deux arbres obtenus en coupant le fil partagé. Premièrement, le premier arbre doit produire un sur au moins une des trois cases positives de chaque bloc. Sinon, sur ces six cases, on pourrait éteindre les autres fils de la seconde formule et la vérifier avec les quatre fils de poids un. Deuxièmement, le signal partagé seul ne peut pas suffire à activer la sortie. S’il suffisait, on pourrait réaliser la sortie par le OU du premier arbre et du second avec le signal fixé à zéro, puis appliquer la même obstruction de poids à l’arbre obtenu.

On choisit une de ces cases positives par bloc. Chacune active une ligne et une colonne. Le premier arbre doit lire au moins un de ces deux fils pour s’allumer. S’il lit les deux, le second arbre ne voit plus que le signal partagé actif, ce qui vient d’être exclu. Il lit donc exactement un des deux. Parmi trois blocs, deux font le même choix, ligne ou colonne. En prenant la ligne de l’un et la colonne de l’autre, les deux arbres conservent tous les fils actifs dont ils ont besoin pour accepter. Cette case entre blocs doit pourtant être rejetée. C’est la contradiction.

Pour reproduire le contrôle, compiler `PositiveCore.lean` puis `ExactThreeCopies.lean` avec les modules du journal accessibles à Lean, notamment `CutTrees`, `FourWireCore` et `ExactTwoCopies`. Les minima pour une, deux et trois copies sont maintenant respectivement 8, 16 et 25. Le cas de quatre copies reste une question distincte. Le résultat concerne l’extension du graphe de L-meta-20782 aux trois copies et constitue une contribution au journal.

### 27 novembre — Couplage parfait 3 × 3 avec deux portes OU imposées

L-meta-27732 demande un circuit d’au plus 11 portes qui reconnaît les graphes bipartis à trois sommets de chaque côté admettant un couplage parfait. Le circuit commence par OU(0,4) et OU(2,7), utilise la dernière porte comme sortie et réutilise chaque sortie intermédiaire. L-meta-27733 demande de réfuter exactement cet énoncé. La [preuve Lean de L-meta-27733](https://github.com/Alexrollo64/pequalnp-proofs/blob/ce986b4455406a3425d58993b866d0b74bf85496/lean/PEqualNP/Outside/L_meta_27733.lean) établit une borne inférieure de 12 portes sous ces contraintes.

Pour chacune des neuf entrées, la preuve exhibe deux graphes qui diffèrent seulement sur cette entrée. Les deux portes initiales donnent les mêmes réponses sur ces graphes, alors que l’existence d’un couplage parfait change. Il faut donc que les portes suivantes lisent directement chacune des neuf entrées. Elles doivent aussi lire chacune des sorties des g − 1 portes intermédiaires. Ces g − 2 portes disposent en tout d’au plus 2(g − 2) places, ce qui impose 9 + (g − 1) ≤ 2(g − 2), donc g ≥ 12. La preuve ne suppose pas qu’un circuit de 12 portes existe.

Le contrôle officiel local de L-meta-27733 (format et compilation Lean 4.36.0) a réussi. La branche du fork contient un commit et le seul fichier attribué. À la clôture de cette session, GitHub avait refusé la création de la PR vers le projet (HTTP 403). Le bureau a confirmé les libérations de L-meta-27732 pour `statement_seems_false` et de L-meta-27733 pour `other`. La preuve vérifiée est disponible pour une nouvelle tentative de soumission officielle.

### 27 novembre — Couplage parfait, deux portes initiales sur quatre arêtes distinctes

[DisjointMatching.lean](DisjointMatching.lean) prouve une généralisation de la borne de L-meta-27733 pour la fonction de couplage parfait sur le graphe biparti 3 × 3. Les deux premières portes peuvent lire deux paires disjointes quelconques de deux arêtes distinctes. Chacune peut être ET ou OU. Tout circuit de fan-in au plus deux qui calcule la fonction, utilise sa dernière porte comme sortie et relit chaque résultat intermédiaire a au moins 12 portes. Le noyau de Lean 4.36 a contrôlé le théorème `Alexrollo64.DisjointMatching.lower` avec les axiomes usuels `propext`, `Classical.choice` et `Quot.sound`.

Pour chaque arête i, on peut trouver un graphe où changer uniquement i change la réponse, tout en fixant une autre arête j quelconque à la valeur souhaitée. Lorsque i entre dans une des deux premières portes, on fixe son partenaire à 1 pour OU ou à 0 pour ET. La porte masque alors le changement de i. La seconde paire est disjointe et conserve sa valeur. Chacune des neuf arêtes doit donc être relue directement après ces deux portes. Le comptage des lectures des neuf entrées et des sorties intermédiaires donne la borne. Le [calcul Python indépendant](matching-openings.py) retrouve les neuf témoins pour chacune des 1 512 configurations (à permutation des deux portes près). L’existence d’un circuit à 12 portes reste ouverte dans ce travail.

### 27 novembre — Deux portes qui partagent une entrée

[OverlapMatching.lean](OverlapMatching.lean) prolonge la preuve de [DisjointMatching.lean](DisjointMatching.lean) au cas où les deux premières portes ET ou OU lisent une même arête du graphe biparti 3 × 3. La borne de 12 portes s’applique à **972 des 1 008 configurations** comptées à permutation des deux portes près. Les hypothèses sur les lectures, la dernière sortie et la réutilisation de chaque sortie intermédiaire sont celles du résultat précédent.

Soit i l’arête commune, et j et k les deux autres entrées. Pour cacher un changement de i aux deux portes à la fois, le partenaire d’une porte OU doit être présent et celui d’une porte ET absent. Le lemme `masked` construit deux graphes qui diffèrent sur i et dont un seul possède un couplage parfait, tout en imposant ces deux valeurs. Pour le graphe qui admet un couplage, il suffit de choisir un des deux couplages parfaits passant par i puis d’ajouter les partenaires qui doivent être présents. La lecture directe des neuf entrées est alors nécessaire après les deux portes, ce qui donne la borne par comptage. Le noyau de Lean 4.36 a contrôlé `Alexrollo64.OverlapMatching.lower` avec les trois axiomes usuels. Compiler d’abord le module DisjointMatching, puis OverlapMatching avec son répertoire dans LEAN_PATH.

Le [contrôle Python indépendant](overlap-census.py) parcourt les 512 graphes pour chaque configuration. Les 36 exceptions sont précisément deux portes ET dont les deux partenaires absents rencontrent à eux deux les deux couplages parfaits passant par l’arête commune. On ne peut alors masquer un changement de cette arête en conservant un couplage qui en dépend. Cela limite cet argument de comptage et laisse ouverte la taille minimale dans ces cas. En fixant i à zéro, le script trouve pour chacun des neuf choix de i un couplage minimal et un ensemble minimal d’arêtes à supprimer pour bloquer tous les couplages avec au moins deux arêtes en commun. Il reste à relier formellement cette observation aux circuits du projet.
