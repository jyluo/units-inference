#!/bin/bash

FILENAME=scanProjectsStats.txt

echo "Files containing JavaFX, AWT, Time, System.ms, or Math trig functions:" > $FILENAME

# grep -rl \
grep -rn \
    -e 'import.*javafx' \
    -e 'import.*java\.awt' \
    -e 'import.*java\.time' \
    -e 'System\.currentTimeMillis()' \
    -e 'sin(.*)' -e 'cos(.*)' -e 'tan(.*)' \
    -e 'asin(.*)' -e 'acos(.*)' -e 'atan(.*)' \
    -e 'sinh(.*)' -e 'cosh(.*)' -e 'tanh(.*)' \
    --include=*.java | sort >> $FILENAME

##### JavaFX

# https://www.tutorialspoint.com/javafx/javafx_architecture.htm

# javafx.animation − Contains classes to add transition based animations such as fill, fade, rotate, scale and translation, to the JavaFX nodes.

# javafx.application − Contains a set of classes responsible for the JavaFX application life cycle.

# javafx.css − Contains classes to add CSS–like styling to JavaFX GUI applications.

# javafx.event − Contains classes and interfaces to deliver and handle JavaFX events.

# javafx.geometry − Contains classes to define 2D objects and perform operations on them.

# javafx.stage − This package holds the top level container classes for JavaFX application.

# javafx.scene − This package provides classes and interfaces to support the scene graph. In addition, it also provides sub-packages such as canvas, chart, control, effect, image, input, layout, media, paint, shape, text, transform, web, etc. There are several components that support this rich API of JavaFX.

# https://www.tutorialspoint.com/javafx/javafx_application.htm

##### Java AWT

# https://www.tutorialspoint.com/awt/awt_event_handling.htm
