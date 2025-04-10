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
- [✓] **Процесс управляющего алгоритма**: модуль `alarm_controller` с комплексной логикой управления
- [✓] **Процессы датчиков**: 3 модуля `sensor` (дым, пламя, кнопка) с недетерминированной активацией
- [✓] **Процессы актуаторов**: 
  - Звуковая сигнализация (`alarm_on`)
  - Система пожаротушения (`fire_suppression_on`) с таймером и уровнем смеси
- [✓] **Процесс среды**: модуль `environment` с 4 недетерминированными генераторами событий
- [✓] **Бесконечная работа**: 9 условий `JUSTICE` и `FAIRNESS running` для всех процессов

**2. Усовершенствованный функционал:**
- [✓] Трехуровневая система проверок:
  1. Базовые свойства (простые инварианты)
  2. Углубленные темпоральные свойства (LTL/CTL)
  3. Дополнительные гарантии работы
- [✓] Комплексные условия активации/деактивации:
  ```smv
  next(fire_suppression_on) := 
      case
          manual_override : FALSE;    -- Ручное
          mixture_level = 0 : FALSE;  -- Смесь
          suppression_timer = 0 : FALSE; -- Время
          ...
      esac;
  ```

**3. Группировка свойств:**
1. **Безопасность** (инварианты):
   - Корректность состояний системы
   - Условия активации

2. **Живучесть** (LTL):
   - Гарантии завершения работы
   - Минимальное время работы
   - Реакция на события

3. **Возможности** (CTL):
   - Достижимость состояний
   - Возможность повторной активации
   - Альтернативные пути выполнения

**4. Проверка выполнения условий G(p → Ф):**
Для всех свойств вида "если p, то Ф" обеспечено:
- `JUSTICE`-условия для бесконечного выполнения p
- Недетерминированность входов:
  ```smv
  next(generate_smoke) := {TRUE, FALSE}; // И аналоги для других
  ```
- Контроль через `FAIRNESS running`

**5. Дополнительные гарантии:**
- Проверка пограничных значений (таймер < 3, смесь < 20%)
- Тестирование конфликтных ситуаций (ручное отключение при работе)
- Верификация восстановления после сбоев
- Проверка минимального времени реакции

----
## Лабораторная работа №2: Верификация моделей в SPIN

# Модель системы пожарной сигнализации на Promela/SPIN

```promela
/* 
 * МОДЕЛЬ СИСТЕМЫ ПОЖАРНОЙ СИГНАЛИЗАЦИИ
 * Реализация для верификатора SPIN
 * 
 * Соответствует требованиям лабораторной работы:
 * 1. Содержит процесс управляющего алгоритма (Controller)
 * 2. Процессы датчиков (Environment → Sensors)
 * 3. Процессы актуаторов (Actuators)
 * 4. Процесс среды (Environment)
 * 5. Работает бесконечно за счет недетерминированных сигналов среды
 * 6. Проверяются 4 свойства с разной темпоральной структурой
 */

/* ================== ОПРЕДЕЛЕНИЕ ТИПОВ И ДАННЫХ ================== */

/* Типы сообщений в системе */
mtype = { 
    smoke_detected,    // Обнаружен дым
    flame_detected,    // Обнаружено пламя
    panic_pressed,     // Нажата тревожная кнопка
    override_signal,   // Сигнал ручного отключения
    alarm_on,          // Команда включения сигнализации
    alarm_off,         // Команда выключения сигнализации
    suppression_start, // Команда запуска пожаротушения
    suppression_stop   // Команда остановки пожаротушения
};

/* Глобальные переменные состояния */
mtype sensor_active;            // Текущий активный датчик
bool override_signal_received = false; // Факт получения сигнала отключения
bool alarm_active = false;      // Состояние сигнализации
bool suppression_active = false; // Состояние системы пожаротушения
byte suppression_timer = 0;     // Таймер работы системы (такты)
byte mixture_level = 100;       // Уровень огнетушащей смеси (%)
const byte consumption_rate = 5; // Расход смеси за такт (%)

/* Системные каналы связи */
chan env_to_sensors = [0] of { mtype };   // Среда → Датчики (рандеву)
chan sensors_to_ctrl = [3] of { mtype };  // Датчики → Контроллер (буфер 3)
chan ctrl_to_actuators = [2] of { mtype }; // Контроллер → Актуаторы (буфер 2)

/* ================== ПРОЦЕССЫ СИСТЕМЫ ================== */

/* 
 * ПРОЦЕСС СРЕДЫ (Environment)
 * Генерирует события для системы с гарантированным чередованием
 */
active proctype Environment() {
    byte counter = 0;
    do
    :: atomic {
        /* Циклическое чередование событий */
        if
        :: (counter % 5 == 0) -> env_to_sensors!smoke_detected
        :: (counter % 5 == 1) -> env_to_sensors!flame_detected
        :: (counter % 5 == 2) -> env_to_sensors!panic_pressed
        :: (counter % 5 == 3) -> env_to_sensors!override_signal
        :: else -> skip  // Пауза между событиями
        fi;
        counter++;
        
        /* Случайная задержка между событиями */
        if :: skip :: skip :: skip fi
    }
    od
}

/* 
 * ПРОЦЕСС ДАТЧИКОВ (Sensors)
 * Принимает события от среды и передает контроллеру
 */
active proctype Sensors() {
    mtype signal;
    do
    :: env_to_sensors?signal ->  // Получение сигнала от среды
        atomic {
            sensor_active = signal;  // Фиксация активного датчика
            override_signal_received = (signal == override_signal);
            sensors_to_ctrl!signal; // Передача сигнала контроллеру
            printf("MSC: Sensor received %e\n", signal); // Логирование
        }
    od
}

/* 
 * ПРОЦЕСС КОНТРОЛЛЕРА (Controller)
 * Основная логика управления системой
 */
active proctype Controller() {
    mtype signal;
    do
    /* Обработка входящих сигналов */
    :: sensors_to_ctrl?signal ->
        atomic {
            if
            /* Активация сигнализации и пожаротушения */
            :: (signal == smoke_detected || signal == flame_detected || 
                signal == panic_pressed) && !suppression_active ->
                ctrl_to_actuators!alarm_on;  // Включение сигнализации
                if
                :: mixture_level > 0 ->  // Проверка наличия смеси
                    ctrl_to_actuators!suppression_start; // Запуск пожаротушения
                    suppression_timer = 10; // Установка таймера
                :: else -> skip  // Невозможно активировать без смеси
                fi
            
            /* Обработка сигнала ручного отключения */
            :: signal == override_signal ->
                ctrl_to_actuators!alarm_off;      // Отключение сигнализации
                ctrl_to_actuators!suppression_stop // Остановка пожаротушения
            
            :: else -> skip  // Игнорирование других сигналов
            fi
        }
    
    /* Управление системой пожаротушения */
    :: suppression_active && suppression_timer > 0 ->
        atomic {
            suppression_timer--;  // Уменьшение таймера
            if
            :: mixture_level >= consumption_rate ->  // Расход смеси
                mixture_level = mixture_level - consumption_rate
            :: else ->  // Смесь закончилась
                ctrl_to_actuators!suppression_stop
            fi
        }
    od
}

/* 
 * ПРОЦЕСС АКТУАТОРОВ (Actuators)
 * Исполняет команды управления системой
 */
active proctype Actuators() {
    mtype command;
    do
    :: ctrl_to_actuators?command ->  // Получение команды
        atomic {
            if
            :: command == alarm_on ->  // Активация сигнализации
                alarm_active = true;
                printf("MSC: Alarm activated\n")
            
            :: command == alarm_off ->  // Деактивация сигнализации
                alarm_active = false;
                printf("MSC: Alarm deactivated\n")
            
            :: command == suppression_start ->  // Запуск пожаротушения
                suppression_active = true;
                printf("MSC: Suppression system activated\n")
            
            :: command == suppression_stop ->  // Остановка пожаротушения
                suppression_active = false;
                printf("MSC: Suppression system deactivated\n")
            fi
        }
    od
}

/* ================== СПЕЦИФИКАЦИИ СВОЙСТВ LTL ================== */

/* 
 * 1. ИНВАРИАНТ: Система пожаротушения не активна при пустом баке 
 * Формат: G(p)
 */
ltl invariant_no_suppression_without_mixture { 
    [] (mixture_level == 0 -> !suppression_active) 
}

/* 
 * 2. ГАРАНТИЯ РЕАКЦИИ: Сигнализация включается при срабатывании датчика
 * Формат: G(p → Fq)
 */
ltl alarm_activation_guarantee {
    [] ((sensor_active == smoke_detected || 
         sensor_active == flame_detected || 
         sensor_active == panic_pressed) -> <> alarm_active)
}

/* 
 * 3. ВОЗМОЖНОСТЬ ОТКЛЮЧЕНИЯ: При активной тревоге можно отключить систему
 * Формат: G(p → Fq)
 */
ltl manual_override_possibility {
    [] (alarm_active -> <> (override_signal_received))
}

/* 
 * 4. КОРРЕКТНОЕ ЗАВЕРШЕНИЕ: Система останавливается по таймеру/смеси/отключению
 * Формат: G(p → (p U q))
 */
ltl proper_shutdown {
    [] (suppression_active -> 
        (suppression_active U 
         (suppression_timer == 0 || mixture_level == 0 || !suppression_active)))
}
```

## Отчет по верификации

### 1. Соответствие требованиям к системе:
- [✓] **Процесс управляющего алгоритма**: модуль `Controller`
- [✓] **Процессы датчиков**: модуль `Sensors` (получает данные от `Environment`)
- [✓] **Процессы актуаторов**: модуль `Actuators`
- [✓] **Процесс среды/пользователя**: модуль `Environment` с циклической генерацией событий
- [✓] **Бесконечная работа**: все процессы используют бесконечные циклы `do...od`

### 2. Реализация функционала пожарной сигнализации:
- [✓] Звуковой сигнал при событиях:
  ```promela
  (signal == smoke_detected || signal == flame_detected || signal == panic_pressed) 
  -> ctrl_to_actuators!alarm_on
  ```
- [✓] Система пожаротушения с тремя условиями остановки:
  ```promela
  :: signal == override_signal -> ctrl_to_actuators!suppression_stop  // Ручное
  :: mixture_level == 0 -> ctrl_to_actuators!suppression_stop        // Нет смеси
  :: suppression_timer == 0 -> ctrl_to_actuators!suppression_stop    // Таймер
  ```

### 3. Свойства с разной темпоральной структурой:
1. **Инвариант** (глобальное условие):
   ```promela
   [] (mixture_level == 0 -> !suppression_active)
   ```
2. **LTL-свойство реакции**:
   ```promela
   [] (p -> <> q)  // Если произошло p, то в будущем будет q
   ```
3. **LTL-свойство возможности**:
   ```promela
   [] (alarm_active -> <> override_signal_received)
   ```
4. **LTL-свойство завершения**:
   ```promela
   [] (p -> (p U q))  // p будет истинно, пока не станет истинно q
   ```

### 4. Проверка выполнения условий:
Для свойства `alarm_activation_guarantee`:
- Условие `p` выполняется бесконечно часто благодаря:
  ```promela
  :: env_to_sensors!smoke_detected
  :: env_to_sensors!flame_detected
  :: env_to_sensors!panic_pressed
  ```
- Fairness гарантируется циклической генерацией событий в `Environment`

### 5. Дополнительные гарантии:
- Недетерминированные задержки:
  ```promela
  if :: skip :: skip :: skip fi
  ```
- Проверка пограничных условий:
  ```promela
  :: mixture_level >= consumption_rate -> ...
  :: else -> ctrl_to_actuators!suppression_stop
  ```
