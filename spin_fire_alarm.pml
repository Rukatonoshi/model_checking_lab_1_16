/* 
 * МОДЕЛЬ СИСТЕМЫ ПОЖАРНОЙ СИГНАЛИЗАЦИИ
 * 
 * 1. Содержит процесс управляющего алгоритма (Controller)
 * 2. Процессы датчиков (Environment → Sensors)
 * 3. Процессы актуаторов (Actuators)
 * 4. Процесс среды (Environment)
 * 5. Работает бесконечно за счет недетерминированных сигналов среды
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
byte consumption_rate = 5; // Расход смеси за такт (%)

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
            if
            :: mixture_level >= consumption_rate ->  // Расход смеси
                mixture_level = mixture_level - consumption_rate;
                suppression_timer--;  // Уменьшение таймера
            :: else ->  // Смесь закончилась
                ctrl_to_actuators!suppression_stop;
                suppression_timer = 0
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
 * 1. Гарантия отсутствия работы при пустом баке: Система пожаротушения не активна при пустом баке 
 * Формат: G(p)
 */
ltl invariant_no_suppression_without_mixture { 
    [] (mixture_level == 0  -> <> (!suppression_active))
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
