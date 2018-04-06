;Primero debe cargarse la biblioteca de la siguiente forma.
(load "maze_lib.lisp")

(add-algorithm 'breadth-first)
(add-algorithm 'depth-first)
(add-algorithm 'bestfs)
(add-algorithm 'A*)
(add-algorithm 'error-example)

;;;=======================================================================
;;;		Blind-Search
;;;
;;;		Estado:
;;;			Lista donde el primer elemento es la fila actual
;;;			y el segundo elemento es la columna actual
;;;			( 1 1 )
;;;		Operadores:
;;;			((1 0) (1 1) (0 1) (-1 1) (-1 0) (-1 -1) (0 -1) (1 -1)) 
;;;=======================================================================

(defparameter *open* '())
(defparameter *memory* '())
(defparameter *id* -1)
(defparameter *current-ancestor* nil)
(defparameter *operators* '( (:arriba (-1 0)) 
							(:arriba-der (-1 1)) 
							(:der (0 1)) 
							(:abajo-der (1 1))
							(:abajo (1 0)) 
							(:abajo-izq (1 -1)) 
							(:izq (0 -1)) 
							(:arriba-izq (-1 -1)) ))

(defparameter *expanded-nodes* 0)
(defparameter *max-length-open* 0)
(defparameter *start-time* nil)
;;=======================================================================
;;  CREATE-NODE [estado  op]  
;;      estado - Un estado del problema a resolver (sistema)...
;;          op - El operador cuya aplicación generó el [estado]...
;;=======================================================================

(defun create-node (state op) 
	"Construye y regresa un nuevo nodo de búsqueda que contiene al estado y operador recibidos como parámetro "
	(progn (incf *id*)								;;incrementamos primero para que lo último en procesarse sea la respuesta
			(list *id* state *current-ancestor* (second op))))	;;los nodos generados son descendientes de *current-ancestor*

;;=======================================================================
;;  INSERT-TO-OPEN   y   GET-FROM-OPEN  
;;        
;;        Insert-to-open  recibe una lista y una llave que identifica el metodo a usar para insertar:
;;             :depth-first     Inserta los elementos de la lista en orden inverso y por el inicio de la lista
;;             :breadth-first    Inserta los elementos de la lista en orden normal y por el final de la lista
;;        Get-from-open  siempre retira el primer elemento de la lista *open*
;;=======================================================================
(defun insert-into-open (state op method) 
	"Permite insertar nodos de la frontera de busqueda *open* de forma apta para buscar a lo profundo y a lo ancho"
	(let ((node (create-node state op))) 
		( cond ((eql method :depth-first) (push node *open* ))
				((eql method :breadth-first)  (setf *open* (append *open* (list node))))
				(T nil) ))
	(when (< *max-length-open* (length *open* ))
				(setf *max-length-open* (length *open*)))) 

(defun get-from-open ()
	"Recupera el siguiente elemento a revisar de  frontera de busqueda *open*"
	(pop *open*))

;;=======================================================================
;;  VALID-OPERATOR [op, estado]
;;        Predicado.  Indica si es posible aplicar el operador [op] a [estado] segun los recursos
;;=======================================================================
(defun get-mask (op) 
	(cond ((= (first op) -1) 
				(cond ((= (second op) -1) #b1001) 
					((= (second op) 1) #b0011)
					(T  #b0001)))
			((= (first op) 1) 
				(cond ((= (second op) -1) #b1100) 
					((= (second op) 1) #b0110)
					(T  #b0100)) )
			(T (cond ((= (second op) -1) #b1000 ) 
					((= (second op) 1) #b0010)
					(T  #b0000))) ))


(defun valid-operator (op state) 
	"Predicado. Valida la aplicación de un operador a un estado..."
	(let ( (mask (get-mask op)) (walls (get-cell-walls (first state) (second state))))  
		(not (= walls (logior walls mask))) ))

;;=======================================================================
;;  VALID-STATE [state]
;;        Predicado.  Indica si [state]  es valido segun las restricciones del problema
;;======================================================================= (not (= (logand (logior #b1100 #b1010) #b1001) #b1001)
(defun  valid-state? (op new-state cur-state)
"Predicado. Valida  un estado según las restricciones generales del problema...
       el estado tiene estructura: (r c)"
   	(let ( (new-row (first new-state)) 
   			(new-col (second new-state))
   			(cur-row (first cur-state)) 
   			(cur-col (second cur-state)))
   			(if (and (and (>= new-row 0) (< new-row (get-maze-rows)) ) 
    		 		(and (>= new-col 0) (< new-col (get-maze-cols)) ) ) 
   				(let* ((new-walls (get-cell-walls new-row new-col))
   						(cur-walls (get-cell-walls cur-row cur-col))
   						(mask (get-mask op)) 
   						(inv-mask (logxor mask #b1111)) 
   						(compose-mask (logior (logand mask cur-walls) (logand inv-mask new-walls)) ))
   					(or (or (= 0 (first op)) (= 0 (second op)))
   						(and (not (= new-walls (logior new-walls inv-mask))) ;;verifica que si se puede pasar, tmb se puede regresar
   							(not (= (logand compose-mask #b1010) #b1010))    ;;verifica que no esten 2 paredes seguidas
   							(not (= (logand compose-mask #b0101) #b0101))) ) ) 
   				nil ) ))

;;=======================================================================
;;  APPLY-OPERATOR [op, state]
;;        Solución simbólica del problema
;;=======================================================================
(defun apply-operator (op state) 
	"Obtiene el descendiente de [state] al aplicarle  [op]  SIN VALIDACIONES"
	(List (+ (first op) (first state)) (+ (second op) (second state))))

;;=======================================================================
;;  EXPAND [ state]
;;        Construye y regresa una lista con todos los descendientes validos de [state]
;;=======================================================================
(defun expand (state) 
	"Obtiene todos los descendientes válidos de un estado, aplicando todos los operadores en *operators* en ese mismo órden"
	(loop for op in *operators* 
		for i from 0 to (length *operators*)
		with new-state = nil
		do (setf new-state (apply-operator (second op) state))
		do (setf *expanded-nodes* (+ *expanded-nodes* 1))
		;do (print (list op new-state state (valid-state? (second op) new-state state)))
		when (and (valid-operator (second op) state) (valid-state? (second op) new-state state))
			collect (list new-state (list (first op) i)) into childs
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
				do (push (fourth current) *solution*)
					(setf current (locate-node (third current) *memory*) ) )) 
		*solution*))

(defun extract-solution-local (node)
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

(defun display-stats ()
	"Despliega las estadisticas de la solución"
	(format t "Nodos creados: ~A~%" *id* )
	(format t "Nodos expandidos: ~A~%" *expanded-nodes*)
	(format t "Longitud máxima de la Frontera de búsqueda: ~A~%" *max-length-open*)
	(format t "Longitud de la solución: ~A operadores~%" (- (length *solution*) 1))
	(format t "Tiempo para encontrar la solución: ~D segundos~% " (- (get-internal-real-time) *start-time*)) )

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
     (setq  *id*  -1)
     (setq  *current-ancestor*  nil)
     (setq  *solution*  nil))

(defun  blind-search (method)
	"Realiza una búsqueda ciega, por el método especificado y desde un estado inicial hasta un estado meta
	    los métodos posibles son: :depth-first - búsqueda en profundidad
	                              :breadth-first - búsqueda en anchura"
    (reset-all)
    (setf *start-time* (get-internal-real-time))
    (let ( (node nil)
    		(state nil)
    		(childs '())
    		(operator nil)
    		(goal-found nil)
    		(goal (list (aref *goal* 0) (aref *goal* 1)))
    		(start (list (aref *start* 0) (aref *start* 1))) )
    	(insert-into-open start nil method)
    	(loop until (or goal-found (null *open*))
    		do (setq node (get-from-open) 
    				 state (second node) 
    				 operator (fourth node))
				(push node *memory*)
				(cond ((equal goal state) 
						(format t "Éxito. Meta encontrada en ~A intentos~%" (first node))
						(extract-solution node)
						(setf *solution* (rest *solution*))
						;(display-solution *solution*)
						;(display-stats)
						(setf goal-found T))
					(T (setf *current-ancestor* (first node))
						(setf childs (expand state))
						(setf childs (filter-memories childs))
						(loop for child in childs do (insert-into-open (first child) (second child) method))) ))))

(defun breadth-first () (blind-search :breadth-first) )

(defun depth-first () (blind-search :depth-first) )

;;=======================================================================
;;  CREATE-NODE-A [estado  op distance]  
;;      estado - Un estado del problema a resolver (sistema)...
;;          op - El operador cuya aplicación generó el [estado]...
;;	  distance - Distancia manhattan
;;=======================================================================

(defun create-node-A (state op distance lvl) 
	"Construye y regresa un nuevo nodo de búsqueda que contiene al estado y operador recibidos como parámetro "
	(progn (incf *id*)								;;incrementamos primero para que lo último en procesarse sea la respuesta
			(list *id* state *current-ancestor* (second op) distance lvl)))	;;los nodos generados son descendientes de *current-ancestor*

;;=======================================================================
;;  INSERT-TO-OPEN-A
;;        
;;        Insert-to-open  recibe una lista y una llave que identifica el metodo a usar para insertar:
;;             :depth-first     Inserta los elementos de la lista en orden inverso y por el inicio de la lista
;;             :breadth-first    Inserta los elementos de la lista en orden normal y por el final de la lista
;;=======================================================================
(defun insert-into-open-A (state op distance lvl) 
	"Permite insertar nodos de la frontera de busqueda *open* de forma apta para buscar a lo profundo y a lo ancho"
	(let ((node (create-node-A state op distance lvl))) 
		(push node *open* ))
	(when (< *max-length-open* (length *open* ))
				(setf *max-length-open* (length *open*)))) 

(defun fitness (state goal) 
	"Calcula la distancia manhattan entre [state] y [goal]"
	(+ (abs (- (first state) (first goal))) (abs (- (second state) (second goal)))) ) 

(defun quicksort (lst)
	(if (null lst) 
    	nil
    	(let* ((x (first lst))
	     		(r (rest lst))
	     		(fn (lambda (a) (< (f a) (f x) ))))
			(append (quicksort (remove-if-not fn r))
					(list x)
					(quicksort (remove-if fn r))))))

(defun f (node)
	"Calcula la suma de la aptitud y el costo del [node]"
	(let ((lvl (sixth node)) 
		(distance (fifth node)) )
		(+ lvl distance)))

(defun bestfs () 
	"Realiza una búsqueda informada bfs" 
	(reset-all)
	(setf *start-time* (get-internal-real-time))
    (let ( (node nil)
    		(state nil)
    		(childs '())
    		(operator nil)
    		(goal-found nil)
    		(goal (list (aref *goal* 0) (aref *goal* 1)))
    		(start (list (aref *start* 0) (aref *start* 1))) )
    	(insert-into-open-A start nil (fitness start goal) 0)
    	(loop until (or goal-found (null *open*))
    		do (setq node (get-from-open) 
    				 state (second node) 
    				 operator (fourth node))
				(push node *memory*)
				(cond ((equal goal state) 
						(format t "Éxito. Meta encontrada en ~A intentos~%" (first node))
						(extract-solution node)
						(setf *solution* (rest *solution*))
						;(display-solution (extract-solution-local node))
						;(display-stats)
						(setf goal-found T))
					(T (setf *current-ancestor* (first node))
						(setf childs (expand state))
						(setf childs (filter-memories childs))
						(loop for child in childs do (insert-into-open-A (first child) (second child) (fitness (first child) goal) 0))
						(setf *open* (quicksort *open*)) )))))

(defun A* () 
	"Realiza una búsqueda informada" 
	(reset-all)
	(setf *start-time* (get-internal-real-time))
    (let ( (node nil)
    		(state nil)
    		(childs '())
    		(operator nil)
    		(goal-found nil)
    		(goal (list (aref *goal* 0) (aref *goal* 1)))
    		(start (list (aref *start* 0) (aref *start* 1))) )
    	(insert-into-open-A start nil (fitness start goal) 0)
    	(loop until (or goal-found (null *open*))
    		do (setq node (get-from-open) 
    				 state (second node) 
    				 operator (fourth node))
				(push node *memory*)
				(cond ((equal goal state) 
						(format t "Éxito. Meta encontrada en ~A intentos~%" (first node))
						(extract-solution node)
						(setf *solution* (rest *solution*))
						;(display-solution (extract-solution-local node))
						;(display-stats)
						(setf goal-found T))
					(T (setf *current-ancestor* (first node))
						(setf childs (expand state))
						(setf childs (filter-memories childs))
						(loop for child in childs do (insert-into-open-A (first child) (second child) (fitness (first child) goal) (+ 1 (sixth node))))
						(setf *open* (quicksort *open*)) )))))

(start-maze)