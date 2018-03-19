;;;=======================================================================
;;;		Ranas.lisp
;;;			Resuelve el problema de las ranas utilizando búsqueda ciega,
;;;			a lo profundo y a lo ancho.
;;;
;;;		Descripción del problema:
;;;			Ambos grupos de ranas desean cruzar el estanque hacia
;;;			el lado opuesto, pero sólo hay una hilera de rocas…
;;;
;;;			Una rana puede saltar una o dos posiciones (adelante o
;;;			atrás) hacia otra roca, siempre y cuando la roca destino
;;;			se encuentre vacía.
;;;		
;;;		Representación de los estados:
;;;			Lista representando la hilera de rocas con los siguientes 
;;;			valores:
;;;				0 -> roca vacía
;;;				1 -> rana tipo 1
;;;				2 -> rana tipo 2
;;;			
;;;			un valor numerico representando la posicion la roca vacía
;;;			
;;;			( (1 1 1 0 2 2 2) 3)
;;;
;;;		Representación de los operadores:
;;;			Lista que contiene sublistas con el siguiente formato:
;;;				( :dos-izq -2 )
;;;
;;;			donde: 
;;;				dos-izq es una etiqueta como identificador
;;;				y el -2 es un valor positivo o negativo que indica la 
;;;				cantidad de saltos y la dirección
;;;
;;;		Estado Inicial:
;;;			( (1 1 1 0 2 2 2) 3)
;;;
;;;		Estado Meta:
;;;			( (2 2 2 0 1 1 1) 3)
;;;
;;;		Héctor Moreno
;;;		18/Marzo/08
;;;=======================================================================
(defparameter *open* '()) 					; Frontera de busqueda
(defparameter *memory* '())					; Memoria de intentos previos
(defparameter *operators* '((:dos-der -2) 	; Operadores
							(:uno-der -1)
							(:uno-izq 1)
							(:dos-izq 2)) )
(defparameter *id* -1)						; Identificador del ultimo nodo creado
(defparameter *current-ancestor* nil)		; Id del ancestro 
(defparameter *solution* nil)				; Lista donde se genera la solución

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
;;  VALID-OPERATOR [op, estado]
;;        Predicado.  Indica si es posible aplicar el operador [op] a [estado] segun los recursos
;;=======================================================================

(defun valid-operator (op state) 
	"Predicado. Valida la aplicación de un operador a un estado..."
	(let ( (next-pos (+ (second state) (second op))) ) 
		 (and (>= next-pos 0) (< next-pos (length (first state) )) ) ))

;;=======================================================================
;;  APPLY-OPERATOR [op, estado]
;;        Solución simbólica del problema
;;=======================================================================
(defun apply-operator (op state) 
	"Obtiene el descendiente de [estado] al aplicarle  [op]  SIN VALIDACIONES"
	(loop for frog in (first state)
		with next-pos = (+ (second state) (second op))
		collect frog into new-state
		finally (setf (nth (second state) new-state) (nth next-pos new-state))
 				(setf (nth next-pos new-state) 0)
 				(return (list new-state next-pos)) ))

;;=======================================================================
;;  EXPAND [ estado]
;;        Construye y regresa una lista con todos los descendientes validos de [estado]
;;=======================================================================
(defun expand (state) 
	"Obtiene todos los descendientes válidos de un estado, aplicando todos los operadores en *operators* en ese mismo órden"
	(loop for op in *operators* 
		when (valid-operator op state)
		collect (list (apply-operator op state) op) into childs
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
