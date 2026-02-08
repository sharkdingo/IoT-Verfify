package cn.edu.nju.Iot_Verify;

import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;
import org.springframework.scheduling.annotation.EnableAsync;

@SpringBootApplication
@EnableAsync
public class IotVerifyApplication {

	public static void main(String[] args) {
		SpringApplication.run(IotVerifyApplication.class, args);
	}

}
