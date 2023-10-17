package hu.oe.nik.szfmv.detector;
import hu.oe.nik.szfmv.detector.classes.Detector;
import java.awt.Point;


import hu.oe.nik.szfmv.detector.classes.Detector;
import hu.oe.nik.szfmv.environment.World;
import hu.oe.nik.szfmv.environment.models.Collidable;
import org.junit.Assert;
import org.junit.Test;

import java.awt.*;
import java.util.List;

import static org.junit.Assert.assertTrue;


public class DetectorTest {
    World w = new World(800, 600);
    final int magicnumber = 5000;

@Test
public void unitcon_test() throws Exception {
Detector con_recv0 = Detector.getDetector();
Point c3 = null;
Point b2 = null;
Point a1 = null;
con_recv0.getCollidableObjects(a1, b2, c3);
}


    @Test
    public void itHasAllWorldObjects() {
        Detector dec = Detector.getDetector();
        Assert.assertNotEquals(dec.getWorldObjects(new Point(0, 0),
                new Point(magicnumber, 0), new Point(0, magicnumber)).size(), 0);
    }

    // @Test
    // public void onlyCollidableObjects() {
    //     Detector dec = Detector.getDetector();
    //     List<Collidable> obj = dec.getCollidableObjects(new Point(0, 0),
    //             new Point(magicnumber, 0), new Point(0, magicnumber));
    //     assertTrue(Collidable.class.isInstance(obj.get(0)));

    // }
}
