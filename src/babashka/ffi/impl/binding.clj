(ns ^{:no-doc true
      :clj-kondo/config '{:lint-as {babashka.ffi.impl.binding/with-method clojure.core/let}}}
  babashka.ffi.impl.binding
  "JVM callables with lazy, class-local native targets. Loaded on the JVM only."
  (:import [clojure.asm ClassWriter Label Opcodes Type]
           [clojure.lang DynamicClassLoader]
           [java.lang.invoke MethodHandle]
           [java.lang.reflect Constructor UndeclaredThrowableException]))

(set! *warn-on-reflection* true)

(definterface ClassDefiner
  (^Class defineBytes [^String name ^bytes code])
  (lookupDelay []))

(defn- resolve-target [holder]
  ;; Never throw from <clinit>: subsequent calls must see the original lookup
  ;; failure, not ExceptionInInitializerError or NoClassDefFoundError.
  (try
    (let [pd (.lookupDelay ^ClassDefiner (.getClassLoader ^Class holder))]
      (object-array [(cast MethodHandle (force pd)) nil]))
    (catch Throwable t (object-array [nil t]))))

#_{:clj-kondo/ignore [:unused-private-var]}
(defn- call-error [t]
  (if (or (instance? RuntimeException t) (instance? Error t))
    t
    (UndeclaredThrowableException. t)))

#_{:clj-kondo/ignore [:unused-private-var]}
(defn- arity-error [sym expected got]
  (throw (ex-info (str "babashka.ffi: " sym " expects " expected " args, got " got)
                  {:symbol sym})))

#_{:clj-kondo/ignore [:unused-private-var]}
(defn- signature-string [sym args ret]
  (str sym " " (pr-str args) " -> " ret))

(defmacro ^:private with-method [[v writer] access name descriptor & body]
  `(let [~(with-meta v {:tag 'clojure.asm.MethodVisitor})
         (.visitMethod ~(with-meta writer {:tag 'clojure.asm.ClassWriter}) ~access ~name ~descriptor nil nil)]
     (.visitCode ~v)
     ~@body
     (.visitMaxs ~v 0 0)
     (.visitEnd ~v)))

(def ^:private public-static (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_STATIC))
(def ^:private obj "Ljava/lang/Object;")
(def ^:private mh "Ljava/lang/invoke/MethodHandle;")
(def ^:private throwable "Ljava/lang/Throwable;")
(def ^:private helper "babashka/ffi/impl/binding$")

(defn- class-writer ^ClassWriter [name parent interfaces]
  (doto (ClassWriter. ClassWriter/COMPUTE_FRAMES)
    (.visit Opcodes/V1_8 (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL)
            name nil parent (into-array String interfaces))))

(def ^:private loader-constructor
  (delay
    ;; A separate defining loader lets discarded bindings unload. Calling
    ;; DynamicClassLoader.defineClass for every binding would also register
    ;; each generated class in Clojure's process-wide soft-reference cache.
    (let [name (str "babashka/ffi/impl/binding/Loader" (gensym))
          writer (class-writer name "java/lang/ClassLoader" ["babashka/ffi/impl/binding/ClassDefiner"])]
      (.visitEnd (.visitField writer (bit-or Opcodes/ACC_PRIVATE Opcodes/ACC_FINAL) "pd" obj nil nil))
      (with-method [v writer] Opcodes/ACC_PUBLIC "<init>" (str "(Ljava/lang/ClassLoader;" obj ")V")
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitVarInsn v Opcodes/ALOAD 1)
        (.visitMethodInsn v Opcodes/INVOKESPECIAL "java/lang/ClassLoader" "<init>" "(Ljava/lang/ClassLoader;)V" false)
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitVarInsn v Opcodes/ALOAD 2)
        (.visitFieldInsn v Opcodes/PUTFIELD name "pd" obj)
        (.visitInsn v Opcodes/RETURN))
      (with-method [v writer] Opcodes/ACC_PUBLIC "lookupDelay" (str "()" obj)
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitFieldInsn v Opcodes/GETFIELD name "pd" obj)
        (.visitInsn v Opcodes/ARETURN))
      (with-method [v writer] Opcodes/ACC_PUBLIC "defineBytes" "(Ljava/lang/String;[B)Ljava/lang/Class;"
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitVarInsn v Opcodes/ALOAD 1)
        (.visitVarInsn v Opcodes/ALOAD 2)
        (.visitInsn v Opcodes/ICONST_0)
        (.visitVarInsn v Opcodes/ALOAD 2)
        (.visitInsn v Opcodes/ARRAYLENGTH)
        (.visitMethodInsn v Opcodes/INVOKEVIRTUAL "java/lang/ClassLoader" "defineClass"
                          "(Ljava/lang/String;[BII)Ljava/lang/Class;" false)
        (.visitInsn v Opcodes/ARETURN))
      (.visitEnd writer)
      (let [loader (DynamicClassLoader. (.getClassLoader (class resolve-target)))
            cls (.defineClass loader (.replace name \/ \.) (.toByteArray writer) nil)]
        (.getConstructor cls (into-array Class [ClassLoader Object]))))))

(defn- target-code [name n void?]
  (let [writer (class-writer name "java/lang/Object" [])
        flags (bit-or public-static Opcodes/ACC_FINAL)
        ret (if void? "V" "J")
        args (apply str (repeat n "J"))]
    (doseq [[field desc] [["TARGET" mh] ["ERROR" throwable]]]
      (.visitEnd (.visitField writer flags field desc nil nil)))
    (with-method [v writer] Opcodes/ACC_STATIC "<clinit>" "()V"
      (.visitLdcInsn v (Type/getObjectType name))
      (.visitMethodInsn v Opcodes/INVOKESTATIC (str helper "resolve_target") "invokeStatic" (str "(" obj ")" obj) false)
      (.visitTypeInsn v Opcodes/CHECKCAST "[Ljava/lang/Object;")
      (.visitInsn v Opcodes/DUP)
      (.visitInsn v Opcodes/ICONST_0)
      (.visitInsn v Opcodes/AALOAD)
      (.visitTypeInsn v Opcodes/CHECKCAST "java/lang/invoke/MethodHandle")
      (.visitFieldInsn v Opcodes/PUTSTATIC name "TARGET" mh)
      (.visitInsn v Opcodes/ICONST_1)
      (.visitInsn v Opcodes/AALOAD)
      (.visitTypeInsn v Opcodes/CHECKCAST "java/lang/Throwable")
      (.visitFieldInsn v Opcodes/PUTSTATIC name "ERROR" throwable)
      (.visitInsn v Opcodes/RETURN))
    (with-method [v writer] public-static "ensure" "()V"
      (let [done (Label.)]
        (.visitFieldInsn v Opcodes/GETSTATIC name "ERROR" throwable)
        (.visitJumpInsn v Opcodes/IFNULL done)
        (.visitFieldInsn v Opcodes/GETSTATIC name "ERROR" throwable)
        (.visitInsn v Opcodes/ATHROW)
        (.visitLabel v done)
        (.visitInsn v Opcodes/RETURN)))
    (with-method [v writer] public-static "call" (str "(" args ")" ret)
      (let [start (Label.) end (Label.) handler (Label.)]
        (.visitTryCatchBlock v start end handler "java/lang/Throwable")
        (.visitLabel v start)
        (.visitFieldInsn v Opcodes/GETSTATIC name "TARGET" mh)
        (doseq [i (range n)] (.visitVarInsn v Opcodes/LLOAD (* 2 i)))
        (.visitMethodInsn v Opcodes/INVOKEVIRTUAL "java/lang/invoke/MethodHandle" "invokeExact"
                          (str "(" args ")" ret) false)
        (.visitLabel v end)
        (.visitInsn v (if void? Opcodes/RETURN Opcodes/LRETURN))
        (.visitLabel v handler)
        (.visitMethodInsn v Opcodes/INVOKESTATIC (str helper "call_error") "invokeStatic" (str "(" obj ")" obj) false)
        (.visitTypeInsn v Opcodes/CHECKCAST "java/lang/Throwable")
        (.visitInsn v Opcodes/ATHROW)))
    (.visitEnd writer)
    (.toByteArray writer)))

(defn- callable-code [name target n void?]
  (let [writer (class-writer name "clojure/lang/AFn" ["clojure/lang/Fn" "clojure/lang/IObj"])
        coercer "Lclojure/lang/IFn$OL;"
        result "Lclojure/lang/IFn$LO;"
        imap "Lclojure/lang/IPersistentMap;"
        fields (vec (concat [["pd" obj]]
                            (map #(vector (str "c" %) coercer) (range n))
                            [["ret" result] ["m" imap] ["sym" obj] ["argtypes" obj] ["rettype" obj]]))
        ctor (str "(" (apply str (repeat (count fields) obj)) ")V")]
    (doseq [[field desc] fields]
      (.visitEnd (.visitField writer (bit-or Opcodes/ACC_PUBLIC Opcodes/ACC_FINAL) field desc nil nil)))
    (with-method [v writer] Opcodes/ACC_PUBLIC "<init>" ctor
      (.visitVarInsn v Opcodes/ALOAD 0)
      (.visitMethodInsn v Opcodes/INVOKESPECIAL "clojure/lang/AFn" "<init>" "()V" false)
      (doseq [[i [field desc]] (map-indexed vector fields)]
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitVarInsn v Opcodes/ALOAD (inc i))
        (when (not= desc obj) (.visitTypeInsn v Opcodes/CHECKCAST (subs desc 1 (dec (count desc)))))
        (.visitFieldInsn v Opcodes/PUTFIELD name field desc))
      (.visitInsn v Opcodes/RETURN))
    (with-method [v writer] Opcodes/ACC_PUBLIC "invoke" (str "(" (apply str (repeat n obj)) ")" obj)
      (.visitMethodInsn v Opcodes/INVOKESTATIC target "ensure" "()V" false)
      (when-not void?
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitFieldInsn v Opcodes/GETFIELD name "ret" result))
      (doseq [i (range n)]
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitFieldInsn v Opcodes/GETFIELD name (str "c" i) coercer)
        (.visitVarInsn v Opcodes/ALOAD (inc i))
        (.visitMethodInsn v Opcodes/INVOKEINTERFACE "clojure/lang/IFn$OL" "invokePrim" (str "(" obj ")J") true))
      (.visitMethodInsn v Opcodes/INVOKESTATIC target "call" (str "(" (apply str (repeat n "J")) ")" (if void? "V" "J")) false)
      (if void?
        (.visitInsn v Opcodes/ACONST_NULL)
        (.visitMethodInsn v Opcodes/INVOKEINTERFACE "clojure/lang/IFn$LO" "invokePrim" (str "(J)" obj) true))
      (.visitInsn v Opcodes/ARETURN))
    (with-method [v writer] Opcodes/ACC_PUBLIC "throwArity" (str "(I)" obj)
      (.visitVarInsn v Opcodes/ALOAD 0)
      (.visitFieldInsn v Opcodes/GETFIELD name "sym" obj)
      (.visitLdcInsn v (int n))
      (.visitMethodInsn v Opcodes/INVOKESTATIC "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" false)
      (.visitVarInsn v Opcodes/ILOAD 1)
      (.visitMethodInsn v Opcodes/INVOKESTATIC "java/lang/Integer" "valueOf" "(I)Ljava/lang/Integer;" false)
      (.visitMethodInsn v Opcodes/INVOKESTATIC (str helper "arity_error") "invokeStatic" (str "(" obj obj obj ")" obj) false)
      (.visitInsn v Opcodes/ARETURN))
    (with-method [v writer] Opcodes/ACC_PUBLIC "invoke" (str "(" (apply str (repeat 20 obj)) "[Ljava/lang/Object;)" obj)
      (.visitVarInsn v Opcodes/ALOAD 0)
      (.visitIntInsn v Opcodes/BIPUSH 20)
      (.visitVarInsn v Opcodes/ALOAD 21)
      (.visitInsn v Opcodes/ARRAYLENGTH)
      (.visitInsn v Opcodes/IADD)
      (.visitMethodInsn v Opcodes/INVOKEVIRTUAL name "throwArity" (str "(I)" obj) false)
      (.visitInsn v Opcodes/ARETURN))
    (with-method [v writer] Opcodes/ACC_PUBLIC "applyTo" (str "(Lclojure/lang/ISeq;)" obj)
      (let [valid (Label.)]
        (.visitVarInsn v Opcodes/ALOAD 1)
        (.visitMethodInsn v Opcodes/INVOKESTATIC "clojure/lang/RT" "count" (str "(" obj ")I") false)
        (.visitInsn v Opcodes/DUP)
        (.visitVarInsn v Opcodes/ISTORE 2)
        (.visitLdcInsn v (int n))
        (.visitJumpInsn v Opcodes/IF_ICMPEQ valid)
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitVarInsn v Opcodes/ILOAD 2)
        (.visitMethodInsn v Opcodes/INVOKEVIRTUAL name "throwArity" (str "(I)" obj) false)
        (.visitInsn v Opcodes/ARETURN)
        (.visitLabel v valid)
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitVarInsn v Opcodes/ALOAD 1)
        (.visitMethodInsn v Opcodes/INVOKESTATIC "clojure/lang/AFn" "applyToHelper" (str "(Lclojure/lang/IFn;Lclojure/lang/ISeq;)" obj) false)
        (.visitInsn v Opcodes/ARETURN)))
    (with-method [v writer] Opcodes/ACC_PUBLIC "meta" (str "()" imap)
      (.visitVarInsn v Opcodes/ALOAD 0)
      (.visitFieldInsn v Opcodes/GETFIELD name "m" imap)
      (.visitInsn v Opcodes/ARETURN))
    (with-method [v writer] Opcodes/ACC_PUBLIC "withMeta" (str "(" imap ")Lclojure/lang/IObj;")
      (.visitTypeInsn v Opcodes/NEW name)
      (.visitInsn v Opcodes/DUP)
      (doseq [[field desc] fields]
        (if (= field "m")
          (.visitVarInsn v Opcodes/ALOAD 1)
          (do (.visitVarInsn v Opcodes/ALOAD 0)
              (.visitFieldInsn v Opcodes/GETFIELD name field desc))))
      (.visitMethodInsn v Opcodes/INVOKESPECIAL name "<init>" ctor false)
      (.visitInsn v Opcodes/ARETURN))
    (with-method [v writer] Opcodes/ACC_PUBLIC "toString" "()Ljava/lang/String;"
      (doseq [field ["sym" "argtypes" "rettype"]]
        (.visitVarInsn v Opcodes/ALOAD 0)
        (.visitFieldInsn v Opcodes/GETFIELD name field obj))
      (.visitMethodInsn v Opcodes/INVOKESTATIC (str helper "signature_string") "invokeStatic" (str "(" obj obj obj ")" obj) false)
      (.visitTypeInsn v Opcodes/CHECKCAST "java/lang/String")
      (.visitInsn v Opcodes/ARETURN))
    (.visitEnd writer)
    (.toByteArray writer)))

(defn make-binding
  "Creates a fixed-arity callable from a delayed long-carrier MethodHandle `pd`,
  argument coercers `cs`, result converter `ret`, metadata `m` and signature.
  Lookup remains lazy and metadata copies share its result or cached failure."
  [pd cs ret m sym argtypes rettype]
  (let [n (count cs)
        void? (= :void rettype)
        id (gensym)
        target (str "babashka/ffi/impl/binding/Target" id)
        name (str "babashka/ffi/impl/binding/NativeBinding" id)
        loader ^ClassDefiner (.newInstance ^Constructor @loader-constructor
                                          (object-array [(.getClassLoader (class resolve-target)) pd]))
        _ (.defineBytes loader (.replace target \/ \.) (target-code target n void?))
        cls (.defineBytes loader (.replace name \/ \.) (callable-code name target n void?))
        ctor (.getConstructor cls (into-array Class (repeat (+ n 6) Object)))]
    (.newInstance ctor (object-array (concat [pd] cs [ret m sym argtypes rettype])))))
