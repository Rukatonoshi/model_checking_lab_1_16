# Лабораторная работа

> Пожарная сигнализация
>
> Подаётся звуковой сигнал, когда есть дым, пламя, нажата тревожная кнопка.
> После этого включается система пожаротушения, которая работает заданное
> время, или пока не закончится пожаротушительная смесь, или пока эту систему не
> отключат вручную.

----
## Верификация моделей в nuXmv

**1. Соответствие требованиям к системе:**
- [✓] **Процесс управляющего алгоритма**: модуль `alarm_controller`
- [✓] **Процессы датчиков**: модули `sensor` (дым, пламя, кнопка)
- [✓] **Процессы актуаторов**: звуковая сигнализация (`alarm_on`) и система пожаротушения (`fire_suppression_on`) в `alarm_controller`
- [✓] **Процесс среды/пользователя**: модуль `environment` с недетерминированными сигналами
- [✓] **Бесконечная работа**: обеспечена `FAIRNESS running` и `JUSTICE`-условиями

**2. Реализация функционала пожарной сигнализации:**
- [✓] Звуковой сигнал при дыме/пламени/кнопке: `next(alarm_on) := (smoke | flame | panic_button)`
- [✓] Система пожаротушения с тремя условиями остановки:
  ```smv
  next(fire_suppression_on) := 
      case
          manual_override : FALSE;  -- ручное отключение
          mixture_level = 0 : FALSE; -- кончилась смесь
          suppression_timer = 0 : FALSE; -- истекло время
          ...
      esac;
  ```

**3. Свойства с разной темпоральной структурой:**
1. **Инвариант** (проверка во всех состояниях):
   ```smv
   INVARSPEC controller.mixture_level = 0 -> !controller.fire_suppression_on
   ```
2. **LTL-свойство** (линейная временная логика):
   ```smv
   LTLSPEC G (env.generate_override -> X !controller.fire_suppression_on)
   ```
3. **CTL-свойство** (ветвящаяся временная логика):
   ```smv
   CTLSPEC AG ((controller.fire_suppression_on & controller.suppression_timer = 0) -> 
               AX !controller.fire_suppression_on)
   ```

**4. Проверка выполнения условий вида G(p → Ф):**
Для свойства `LTLSPEC G (env.generate_override -> X !controller.fire_suppression_on)`:
- Убеждаемся, что `env.generate_override` выполняется бесконечно часто благодаря:
  ```smv
  JUSTICE env.generate_override
  next(generate_override) := {TRUE, FALSE}; // Недетерминированность
  ```

**5. Дополнительные гарантии:**
- Недетерминированные входы:
  ```smv
  next(generate_smoke) := {TRUE, FALSE}; // Аналогично для других датчиков
  ```
- Ограничения справедливости:
  ```smv
  JUSTICE controller.alarm_on       // Бесконечные срабатывания
  JUSTICE !controller.alarm_on     // Бесконечные отключения
  ```

**Итоговая проверка:**
```sh
nuXmv -int fire_alarm.smv
read_model -i fire_alarm.smv
go
check_invar    # Все инварианты верны
check_ltlspec  # Все LTL-свойства верны 
check_ctlspec  # Все CTL-свойства верны
```

----
## Лабораторная работа №2: Верификация моделей в SPIN

> TODO
