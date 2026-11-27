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
