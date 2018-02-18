# Lusmodelchecker


Pour compiler le projet, si la lib n'est pas encore créer,
se placer dans le répertoire `lmoch` du projet puis taper la commande:
     
     make

Pour lancer le programme, se placer dans le répertoire `src` du projet et entrer la commande:

    ./lmoch [option] ../exemples/<fichier>.lus check
    
Si possible pour pouvez aussi bénéficier d'un exécutable compilé en natif dans le dossier `\_build/`.
Pour lancer ce programme, toujours dans le répertoire `src`, entrer la commande:

    ./_build/lmoch.native [option] ../exemples/<fichier>.lus check


Pour les options d'usages:

	usage: ./lmoch [options] file.lus <main>
  		-parse-only   stops after parsing
  		-type-only   stops after typing
  		-norm-only   stops after normalization
  		-verbose   print intermediate transformations
  		-debug   print debug informations for aez transformations
  		-d   print debug informations for aez transformations
  		-v   print intermediate transformations
  		-ind   manualy set the level on induction
  		-help  Display this list of options
  		--help  Display this list of options


	
																		
