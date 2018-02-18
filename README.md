# Lusmodelchecker


Pour compiler le projet, si la lib n'est pas encore créer,
se placer dans le dossier `lmoch` du projet puis taper la commande:
     
     make

Ensuite se placer dans le dossier `src` du projet et entrer la commande :

    ./lmoch [option] ../exemples/<fichier>.lus check

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


	
																		
