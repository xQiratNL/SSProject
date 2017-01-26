package cf.client;

import java.util.Set;
import java.util.HashSet;

import javafx.application.Application;
import javafx.scene.Group;
import javafx.scene.PerspectiveCamera;
import javafx.scene.Scene;
import javafx.scene.shape.Box;
import javafx.stage.Stage;

public class Viewer extends Application implements Runnable {

	private Set<int[]> marks;
	
//	public Viewer(Set<int[]> marks) {
//		this.marks = marks;
//	}
	
	private Group root;
	
	public void start(Stage stage) {
		// loop through all marks and add them to a Set of elements (nodes).
		
		Box box = new Box(100, 100, 100);
		box.setTranslateX(200);
		box.setTranslateY(200);
		box.setTranslateZ(150);

		PerspectiveCamera camera = new PerspectiveCamera(false);
		camera.setRotate(10);
		root = new Group();
		
		
		// loop through a Set of elements (nodes) and add all of them to the root.
		root.getChildren().add(box);
		
		Scene scene = new Scene(root, 400, 400, true);
		scene.setCamera(camera);
		stage.setScene(scene);
		stage.show();  

	}
	
	public void run() {
		Application.launch();
	}
	
    public static void main(String[] args) {
    	Application.launch();
    }

}
