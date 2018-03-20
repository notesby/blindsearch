;;;=======================================================================
;;;		Glol.lisp
;;;			Resuelve el problema de GLOL utilizando búsqueda ciega,
;;;			a lo profundo y a lo ancho.
;;;
;;;		Descripción del problema:
;;;			Un granjero desea cruzar el río, acompañado de su lobo,
;;;			su oveja y una caja de Legumbres.
;;;			En su lancha sólo cabe uno de esos elementos, además de él como
;;;			remero.
;;;			No deben estar solos, en ninguna orilla, el lobo con la
;;;			oveja, ni la oveja con las legumbres.
;;;		
;;;		Representación de los estados:
;;;			Lista con dos sublistas internas una por cada orilla
;;;			En cada orilla, un T o Nil si hay Lobo (L),Oveja (O), 
;;;			Legumbre (Le) y Granjero (G)
;;;			
;;;			  L Le O G    L Le O G
;;;			(( 1 1 1 1 ) ( 0 0 0 0 ))
;;;
;;;		Representación de los operadores:
;;;			Lista que contiene sublistas con el siguiente formato:
;;;							L Le O
;;;			(:oveja ( 0 0 1 ))
;;;
;;;		Estado Inicial:
;;;			(( 1 1 1 1 ) ( 0 0 0 0 ))
;;;
;;;		Estado Meta:
;;;			(( 0 0 0 0) ( 1 1 1 1 ))
;;;
;;;		Héctor Moreno
;;;		18/Marzo/08
;;;=======================================================================
(defparameter *open* '()) 					; Frontera de busqueda
(defparameter *memory* '())					; Memoria de intentos previos
(defparameter *operators* '((:lobo (1 0 0)) 	; Operadores
							(:legumbre (0 1 0))
							(:oveja (0 0 1))
							(:nada (0 0 0))) )
(defparameter *id* -1)						; Identificador del ultimo nodo creado
(defparameter *current-ancestor* nil)		; Id del ancestro 
(defparameter *solution* nil)				; Lista donde se genera la solución
(defparameter *invalid-states* '( (1 0 1 0) 
								  (0 1 1 0) ))
;;=======================================================================
;;  CREATE-NODE [estado  op]  
;;      estado - Un estado del problema a resolver (sistema)...
;;          op - El operador cuya aplicación generó el [estado]...
;;=======================================================================
(defun create-node (state op) 
	"Construye y regresa un nuevo nodo de búsqueda que contiene al estado y operador recibidos como parámetro "
	(progn (incf *id*)								;;incrementamos primero para que lo último en procesarse sea la respuesta
			(list *id* state *current-ancestor* (first op))))	;;los nodos generados son descendientes de *current-ancestor*

;;=======================================================================
;;  INSERT-TO-OPEN   y   GET-FROM-OPEN  
;;        
;;        Insert-to-open  recibe una lista y una llave que identifica el metodo a usar para insertar:
;;             :depth-first     Inserta los elementos de la lista en orden inverso y por el inicio de la lista
;;             :breath-first    Inserta los elementos de la lista en orden normal y por el final de la lista
;;        Get-from-open  siempre retira el primer elemento de la lista *open*
;;=======================================================================
(defun insert-into-open (state op method) 
	"Permite insertar nodos de la frontera de busqueda *open* de forma apta para buscar a lo profundo y a lo ancho"
	(let ((node (create-node state op))) 
		( cond ((eql method :depth-first) (push node *open* ))
				((eql method :breath-first)  (setf *open* (append *open* (list node))))
				(T nil) ))) 

(defun get-from-open ()
	"Recupera el siguiente elemento a revisar de  frontera de busqueda *open*"
	(pop *open*))

;;=======================================================================
;;  BARGE-SHORE [state]
;;        Regresa la orilla del rio en la que se encuentra la barca en  [state]
;;           0 - Orilla origen (primer sublista del estado)
;;           1 - Orilla destino (segunda sublista del estado)
;;=======================================================================
(defun  barge-shore (state)
"Regresa la orilla del río en la que se encuentra la barca en el estado recibido como parámetro:  0 - origen  1 - destino"
     (if  (= 1 (fourth (first  state)))  0  1))

;;=======================================================================
;;  VALID-OPERATOR [op, state]
;;        Predicado.  Indica si es posible aplicar el operador [op] a [state] segun los recursos
;;=======================================================================
(defun valid-operator (op state)
	"Predicado. Valida la aplicación de un operador a un estado..."
	(let ((shore (nth (barge-shore state) state))) 
		(loop for rm-animal in (second op)
				for animal in shore
				when (> 0 (- animal rm-animal ))
					do (return Nil)
				finally (return T) ) ))

;;=======================================================================
;;  VALID-STATE [state]
;;        Predicado.  Indica si [state]  es valido segun las restricciones del problema
;;=======================================================================
(defun  valid-state? (state)
"Predicado. Valida  un estado según las restricciones generales del problema...
       el estado tiene estructura:  [(<l0><le0><o0><g0>) (<l1><le1><o1><g1>)]"
    (loop for shore in state
    	with is-invalid = Nil
    	when is-invalid
    		do (return Nil)
  	 	do (loop for invalid-shore in *invalid-states*
  	 		when is-invalid
  	 			do (return Nil)
  	 		do (setf is-invalid T)
  	 			(loop for animal1 in invalid-shore
  	 				 for animal2 in shore
  	 			do (setf is-invalid (and (= animal1 animal2) is-invalid) ))) 
  	 	finally (return (not is-invalid))))

;;=======================================================================
;;  APPLY-OPERATOR [op, state]
;;        Solución simbólica del problema
;;=======================================================================
(defun flip (bit)  (boole  BOOLE-XOR  bit  1))

(defun apply-operator (op state) 
	"Obtiene el descendiente de [state] al aplicarle  [op]  SIN VALIDACIONES"
	(loop for shore in state 
		collect (loop for animal in shore
					  for animal2 in (second op)
					  	if (= (fourth shore) 1)
							collect (- animal animal2) into new-shore
						else
							collect (+ animal animal2) into new-shore
						finally (return (append new-shore (list (flip (fourth shore))) )) ) ))

;;=======================================================================
;;  EXPAND [ state]
;;        Construye y regresa una lista con todos los descendientes validos de [state]
;;=======================================================================
(defun expand (state) 
	"Obtiene todos los descendientes válidos de un estado, aplicando todos los operadores en *operators* en ese mismo órden"
	(loop for op in *operators* 
		with new-state = nil
		do (setf new-state (apply-operator op state))
		when (and (valid-operator op state) (valid-state? new-state))
			collect (list new-state op) into childs
		finally (return childs)))

;;=======================================================================
;;  REMEMBER-STATE?  y  FILTER-MEMORIES
;;        Permiten administrar la memoria de intentos previos
;;=======================================================================
(defun remember-state? (state memory)
	"Busca un estado en una lista de nodos que sirve como memoria de intentos previos"
	(cond ((null memory) nil )
			((equal (second (first memory)) state) T)
			(T (remember-state? state (rest memory))) ))

(defun filter-memories (child-states)
	"Filtra una lista de estados-y-operadores quitando aquellos elementos cuyo estado está en la memoria *memory*
     la lista de estados y operadores tiene estructura: [(<estado> <op>) (<estado> <op>) ... ]"
    (cond ((null child-states) nil)
    		((remember-state? (first (first child-states)) *memory*) 
    			(filter-memories (rest child-states)))
			(T (cons (first child-states) (filter-memories (rest child-states)))) ))

;;=======================================================================
;;  EXTRACT-SOLUTION  y  DISPLAY-SOLUTION
;;       Recuperan y despliegan la secuencia de solucion del problema...
;;       extract-solution   recibe un nodo (el que contiene al estado meta) que ya se encuentra en la memoria y
;;                                    rastrea todos sus ancestros hasta llegar  al  nodo que contiene al estado inicial...
;;       display-solution  despliega en pantalla la lista global *solucion* donde ya se encuentra, en orden correcto,
;;                                    el proceso de solución del problema...
;;=======================================================================

(defun extract-solution (node)
	"Rastrea en *memory* todos los descendientes de [node] hasta llegar al estado inicial"
	(labels 
		((locate-node (id nodes) 
			(cond ((null nodes) nil)
					((eql (first (first nodes)) id) (first nodes))
					(T (locate-node id (rest nodes))))))
		(let ((current (locate-node (first node) *memory*)) )
			(loop while (not (null current)) 
				do (push current *solution*)
					(setf current (locate-node (third current) *memory*) ) )) 
		*solution*))

(defun display-solution (nodes)
	"Despliega la solución en forma conveniente y numerando los pasos"
	(format t "Solución con ~A  pasos:~%~%" (- (length nodes) 1))
	(loop for i from 0 to (- (length nodes) 1)
		with node = nil
		do (setq node (nth i nodes))
		if (= i 0)
			do (format t "Inicio en: ~A~%" (second  node))
		else
			do (format t "\(~2A\)  aplicando ~20A se llega a ~A~%"  i (fourth  node)  (second  node)) ))


;;=======================================================================
;;  RESET-ALL  y  BLIND-SEARCH
;;
;;       Recuperan y despliegan la secuencia de solucion del problema...
;;       extract-solution   recibe un nodo (el que contiene al estado meta) que ya se encuentra en la memoria y
;;                                    rastrea todos sus ancestros hasta llegar  al  nodo que contiene al estado inicial...
;;       display-solution  despliega en pantalla la lista global *solucion* donde ya se encuentra, en orden correcto,
;;                                    el proceso de solucion del problema...
;;=======================================================================

(defun reset-all () 
"Reinicia todas las variables globales para iniciar una nueva búsqueda..."
     (setq  *open*  nil)
     (setq  *memory*  nil)
     (setq  *id*  0)
     (setq  *current-ancestor*  nil)
     (setq  *solution*  nil))

(defun  blind-search (initial-state goal-state method)
	"Realiza una búsqueda ciega, por el método especificado y desde un estado inicial hasta un estado meta
	    los métodos posibles son: :depth-first - búsqueda en profundidad
	                              :breath-first - búsqueda en anchura"
    (reset-all)
    (let ( (node nil)
    		(state nil)
    		(childs '())
    		(operator nil)
    		(goal-found nil) )
    	(insert-into-open initial-state nil method)
    	(loop until (or goal-found (null *open*))
    		do (setq node (get-from-open) 
    				 state (second node) 
    				 operator (fourth node))
				(push node *memory*)
				(cond ((equal goal-state state) 
						(format t "Éxito. Meta encontrada en ~A intentos~%" (first node))
						(display-solution (extract-solution node))
						(setf goal-found T))
					(T (setf *current-ancestor* (first node))
						(setf childs (expand state))
						(setf childs (filter-memories childs))
						(loop for child in childs do (insert-into-open (first child) (second child) method))) ))))  

;;=======================================================================
;;=======================================================================



