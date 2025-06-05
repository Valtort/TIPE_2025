
# Projet-TIPE : Model-Checking

## Objectif

Ce projet a pour but de mettre en œuvre un **vérificateur de modèle (model checker)** en utilisant la logique temporelle linéaire (LTL) dans le langage OCaml.  
L'objectif est de déterminer si une **structure de Kripke** satisfait une formule LTL donnée à l'aide d'automates de Büchi.
L'interêt principal est de modéliser un algorithme à l'aide d'une structure de Kripke, et de montrer qu'il vérifie une certaine formule LTL (un invariant par exemple si on veut montrer la correction de notre algorithme).

---

## Fonctionnalités principales

Le projet s'articule autour de 6 grandes étapes :

1. **Implémentation de la logique LTL**
   - Représentation de formules LTL en OCaml.
   - Conversion en **forme normale négative (FNN)**.

2. **Structures de Kripke**
   - Modélisation d'états, transitions et étiquettes de propositions atomiques.

3. **Traduction en automate de Büchi**
   - Conversion d'une structure de Kripke en un automate de Büchi.

4. **Conversion LTL → automate de Büchi**
   - Génération d’un automate de Büchi acceptant toutes les exécutions satisfaisant une formule LTL donnée.

5. **Intersection d'automates de Büchi**
   - Calcul de l’intersection entre deux automates de Büchi.

6. **Test de vacuité**
   - Vérification si l’automate résultant accepte un mot infini (i.e., non-vide).

## I) Implémentation de la logique LTL
