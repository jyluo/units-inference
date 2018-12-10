#!/bin/sh

# Running into sym-link issues

# run from java-projects folder
for dir in $( ls -d -- */ | sort -g ); do
    echo "unzipping dir $dir"
    cd $dir

    for zip in *.zip; do
        dirname=`echo $zip | sed 's/\.zip$//'`
        echo "unzipping $zip into $dirname"

        if mkdir "$dirname"; then
            if cd "$dirname"; then
                # unzip is non destructive to the zip file
                unzip ../"$zip"
                cd ..
                # Uncomment to delete the original zip file
                # rm -f $zip
            else
                echo "Could not unpack $zip - cd failed"
            fi
        else
            echo "Could not unpack $zip - mkdir failed"
        fi
    done

    cd ..
done
